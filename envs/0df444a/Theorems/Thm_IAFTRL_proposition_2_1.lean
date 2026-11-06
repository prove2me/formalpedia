-- Prove2me | Theorems.Thm_IAFTRL_proposition_2_1
-- name    : IAFTRL.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:27.344895+00:00
-- url     : https://prove2.me/theorems/e209dde9-80d0-4deb-bbe4-9b4dbed01624
-- title:
--   Proposition 2.1 — regret of IA-FTRL for every fixed feasible allocation
-- statement:
--   There is an absolute constant $c_0>0$ such that the following holds for every dimension $d\ge1$ and every finite action set $\mathcal A$ in the unit ball of $\mathbb R^d$ spanning $\mathbb R^d$, with $K=|\mathcal A|$.
--   1. **Adversarial regime (2.4).** For every execution of IA-FTRL for $T\ge1$ rounds against an adaptive environment and every comparator $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\big(d\log K+\sqrt{dT\log K}\big).
--   $$
--   2. **Corrupted stochastic regime (2.5).** For every loss vector $\theta$ with $\|\theta\|_{\mathcal A}\le1$ and a unique optimal action $a^*$, every $\Delta_0\in(0,1]$ with $\Delta_0\le\Delta(a)$ for all $a\ne a^*$, and every feasible sampling allocation $n$ of (1.2), there is a constant $M$ (depending on the instance and on $n$ only) such that for every execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with any budget $C\ge0$ and every $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\Big(c^n(\mathcal A,\theta)\log K\cdot\log T+\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C\Big)+M .
--   $$
--
--   Both guarantees hold for the same algorithm, which knows neither the regime nor $\theta$, $C$, $T$ or $\Delta_{\min}$.
--
--   **Formalization Note** $O(\cdot)$ is read with one absolute constant. The paper's $J_{d,K,\Delta_{\min}}=O(\sqrt{d\log K}\Delta_{\min}^{-128/255})$ is absorbed into the $c_0$-term, and $c_0M_n$ into $M$, which is chosen before the probability space, the horizon, the budget and the run.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → one absolute constant $c_0>0$ chosen before the dimension, the action set and the instance; reason: the stronger of the two readings; an instance-dependent constant in front of the leading term would empty the statement, and the proof's constants are absolute ((C.3)–(C.5), (D.7), Proposition D.2)
--   - reading: the constant $M$ and $J_{d,K,\Delta_{\min}}$, "independent of $T$, $C$" → $\exists M$ after $(d,K,\mathcal A,\theta,a^*,\Delta_0)$ and before the probability space, $T$, $C$ and the run; $J$ absorbed into $c_0\sqrt{d\log K}\,\Delta_0^{-128/255}$; reason: $M$ is defined in (D.5) from instance constants only; $J=O(\sqrt{d\log K}\Delta_{\min}^{-128/255})$
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment's fresh pre-action randomization does not reveal it to the learner"
--   - reading: corrupted regime: fixed $\theta$ → fixed $\theta$ with $\|\theta\|_{\mathcal A}\le1$; reason: the stochastic regime's assumption (p.5), used in the corrupted regime as $0\le\kappa_t\le2$ (p.86)
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the proof uses only the objective comparison (C.1)/(D.158)
--   - generalization: $\Delta_{\min}\in(0,1]$ → any $\Delta_0\in(0,1]$ with $\Delta_0\le\Delta(a)$ for all $a\ne a^*$; reason: at $\Delta_0=\Delta_{\min}$ (assumed $\le1$ by the paper) this is the source's bound; also covers $K=1$, where $\Delta_{\min}$ is undefined and the regret is $0$
--   - encoding: (2.1), (2.3d)–(2.3f) → softmax closed form of (2.1); computable forms of (2.3d)–(2.3f); reason: the paper states both equivalences itself (pp.18–19, (D.151))
--   - encoding: $\sup_{u\in\mathcal A}\mathrm{Reg}_T$, rounds $1,\dots,T$, actions as a set → a bound for every comparator action $u$; 0-based rounds with $\beta_{t+1}$; `Fin K` actions with the `Fin K` order for ties; reason: Lean conventions; same instances
--   - encoding: horizon $T$, dimension $d$ → $T\ge1$, $d\ge1$; reason: $\log T$ is undefined at $T=0$ (where the regret is $0$); the paper works in $\mathbb R^d$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.2, Proposition 2.1, p.20, Eqs. (2.4)–(2.5)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost

namespace IAFTRL

open Matrix MeasureTheory

/-- **Proposition 2.1 (regret for every fixed feasible allocation).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Proposition 2.1,
p.20: "For linear bandits with finite action sets, IA-FTRL guarantees
`Reg_T = O(d log K + √(dT log K))`, (2.4) in the adversarial regime. Simultaneously, for every
feasible sampling allocation `n` in (1.2), IA-FTRL guarantees
`Reg_T = O(c^n(𝒜, θ) log K · log T + M_n + J_{d,K,Δ_min}√C)`, (2.5) in the corrupted stochastic regime,
where `J_{d,K,Δ_min} = O(√(d log K) Δ_min^{−128/255})`, and `M_n` is a finite constant depending on the
instance `(𝒜, θ)` and the sampling allocation `n`, but independent of `T` and `C`."

There is an absolute constant `c₀ > 0` such that for every dimension `d ≥ 1` and every spanning
finite action set `𝒜` in the unit ball of `ℝ^d`, with `K = |𝒜|`:
1. (2.4) every execution of IA-FTRL for `T ≥ 1` rounds against an adaptive environment has
   `Reg_T(u) ≤ c₀(d log K + √(dT log K))` for every comparator `u ∈ 𝒜`;
2. (2.5) for every `θ` with `‖θ‖_𝒜 ≤ 1` and unique optimal action `a*`, every `Δ₀ ∈ (0, 1]` with
   `Δ₀ ≤ Δ(a)` for all `a ≠ a*`, and every feasible sampling allocation `n` of (1.2), there is a
   constant `M` such that every execution of IA-FTRL for `T ≥ 1` rounds in the corrupted stochastic
   regime with any budget `C ≥ 0` has
   `Reg_T(u) ≤ c₀(c^n(𝒜, θ) log K · log T + √(d log K) Δ₀^{−128/255} √C) + M` for every `u ∈ 𝒜`.

**Formalization Note.** `O(·)` is read with one absolute constant `c₀`, chosen before the instance.
`M` (the paper's `c₀M_n`) is chosen after `(d, K, 𝒜, θ, a*, Δ₀, n)` and before the probability space,
the horizon `T`, the budget `C` and the run, so it is independent of `T` and `C`; `J` is absorbed into
`c₀√(d log K)Δ₀^{−128/255}`. `Δ₀` is any lower bound in `(0, 1]` on the gaps; at `Δ₀ = Δ_min ≤ 1` this
is (2.5). The bound on every `Reg_T(u)` is the bound on `sup_u Reg_T(u)`. -/
theorem proposition_2_1 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : Run d K Ω), 1 ≤ T → IsIAFTRLRun P arms T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K))) ∧
      (∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M) := by sorry

end IAFTRL
