-- Prove2me | Theorems.Thm_IAFTRL_proposition_2_1_stochastic
-- name    : IAFTRL.proposition_2_1_stochastic
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:24:00.522201+00:00
-- url     : https://prove2.me/theorems/4d8596d7-b9b0-4434-beb5-3dc99d14479e
-- title:
--   Proposition 2.1 (2.5) — corrupted stochastic regret for every fixed feasible allocation
-- statement:
--   This is the corrupted stochastic half, (2.5), of Proposition 2.1.
--
--   There is an absolute constant $c_0>0$ with the following property. Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Let $\theta$ satisfy $\|\theta\|_{\mathcal A}=\max_{a\in\mathcal A}|a^\top\theta|\le1$ and have a unique optimal (loss-minimizing) action $a^*$, and let $\Delta_0\in(0,1]$ satisfy $\Delta_0\le\Delta(a)=(a-a^*)^\top\theta$ for all $a\ne a^*$. Let $n$ be any feasible sampling allocation of (1.2), with information-acquisition cost $c^n(\mathcal A,\theta)=\sum_a n_a\Delta(a)$. Then there is a constant $M$, depending only on these data, such that every execution of IA-FTRL for $T\ge1$ rounds in the corrupted stochastic regime with corruption budget $C\ge0$ satisfies, for every comparator $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\Big(c^n(\mathcal A,\theta)\log K\cdot\log T+\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C\Big)+M .
--   $$
--
--   Together with the adversarial bound of Proposition D.2, this gives Proposition 2.1. Applied at the allocation of Lemma C.3, it yields the $c^*(\mathcal A,\theta)\log K\cdot\log T$ rate of Theorem 2.1.
--
--   **Formalization Note** This is the second conjunct of `IAFTRL.proposition_2_1`, with its own absolute constant and the same quantifier order: $c_0$ is chosen before the instance, and $M$ (the paper's $c_0M_n$) after $(d,K,\mathcal A,\theta,a^*,\Delta_0,n)$ but before the probability space, $T$, $C$ and the run. The paper's $J_{d,K,\Delta_{\min}}$ is absorbed into $c_0\sqrt{d\log K}\,\Delta_0^{-128/255}$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Proposition 2.1, p.20, bound (2.5); M_n defined in (D.5)

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

/-- **Proposition 2.1, corrupted stochastic part (2.5).** Zhao–Tan, *Best-of-Both-Worlds FTRL for
Linear Bandits*, arXiv:2611.01299, Proposition 2.1, p.20: "Simultaneously, for every feasible
sampling allocation `n` in (1.2), IA-FTRL guarantees
`Reg_T = O(c^n(𝒜, θ) log K · log T + M_n + J_{d,K,Δ_min}√C)`, (2.5) in the corrupted stochastic
regime, where `J_{d,K,Δ_min} = O(√(d log K) Δ_min^{−128/255})`, and `M_n` is a finite constant
depending on the instance `(𝒜, θ)` and the sampling allocation `n`, but independent of `T` and `C`."

There is an absolute constant `c₀ > 0` such that for every dimension `d ≥ 1`, every spanning finite
action set `𝒜` in the unit ball of `ℝ^d` with `K = |𝒜|`, every `θ` with `‖θ‖_𝒜 ≤ 1` and unique
optimal action `a*`, every `Δ₀ ∈ (0, 1]` with `Δ₀ ≤ Δ(a)` for all `a ≠ a*`, and every feasible
sampling allocation `n` of (1.2), there is a constant `M` such that every execution of IA-FTRL for
`T ≥ 1` rounds in the corrupted stochastic regime with any budget `C ≥ 0` has
`Reg_T(u) ≤ c₀(c^n(𝒜, θ) log K · log T + √(d log K) Δ₀^{−128/255} √C) + M` for every `u ∈ 𝒜`.

**Formalization Note.** This is the second conjunct of `IAFTRL.proposition_2_1`, with its own
absolute constant and the same quantifier order: `c₀` before the instance, `M` (the paper's `c₀M_n`)
after `(d, K, 𝒜, θ, a*, Δ₀, n)` and before the probability space, `T`, `C` and the run. -/
theorem proposition_2_1_stochastic : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by sorry

end IAFTRL
