-- Prove2me | Theorems.Thm_IAFTRL_theorem_3_1
-- name    : IAFTRL.theorem_3_1
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:38:26.70622+00:00
-- url     : https://prove2.me/theorems/4954658d-8d83-4d43-83b7-b6029b56356c
-- title:
--   Theorem 3.1 — regret of GIA-FTRL in the sharp action case
-- statement:
--   **Setting.** Let $\mathcal A\subseteq\mathbb B^d$ ($d\ge1$) be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$. GIA-FTRL (Algorithm 2) runs on a compact generator $\mathcal B$, meaning $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$, with $k=\dim\operatorname{aff}(\mathrm{Conv}\,\mathcal B)\ge1$ and a fixed enumeration of $\mathbb Q^d$. The regret against a comparator $u$ is $\mathrm{Reg}_T(u)=\mathbb E\big[\sum_{t\le T}(A_t-u)^\top\theta_t\big]$, and $\mathrm{Reg}_T=\sup_{u\in\mathcal A}\mathrm{Reg}_T(u)$. In the corrupted stochastic regime, $\theta_t=\theta+c_t$ with $\|\theta\|_{\mathcal A}\le1$ and $\sum_{t\le T}\|c_t\|_{\mathcal A}\le C$ almost surely, and $\theta$ has a unique optimal action $a^*\in\mathcal A$. All objects are those of the definition `IAFTRL_GIAFTRL`.
--
--   There is an absolute constant $c_0>0$ with the following two properties.
--
--   1. **Adversarial regime.** Every run of GIA-FTRL satisfies, for all $T\ge2$ and all $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\,d\sqrt T\log T. \tag{3.8}
--   $$
--   2. **Corrupted stochastic regime.** If the instance $(\mathcal A,\theta)$ satisfies the sharpness condition (1.3), then there are finite constants $M_{\mathcal A,\theta}$ and $J^{\mathrm{cor}}_\theta$, independent of $T$ and $C$, such that for all $T\ge1$, $C\ge0$ and $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\,c^*_{\mathrm{ctr}}(\mathcal A,\theta)\,d\log T+M_{\mathcal A,\theta}+J^{\mathrm{cor}}_\theta\sqrt C\log_+(C), \tag{3.10}
--   $$
--   where $\log_+(x)=\log\max\{e,x\}$ and $c^*_{\mathrm{ctr}}$ is the centered information-acquisition complexity of Definition 1.2.
--
--   This is the paper's main guarantee for compact action sets. It gives a single FTRL-based algorithm with $O(d\sqrt T\log T)$ adversarial regret and, on sharp instances, $O(c^*_{\mathrm{ctr}}d\log T)$ stochastic regret plus an $O(\sqrt C\log_+C)$ corruption term.
--
--   **Formalization Note.**
--   - $O(\cdot)$ is the absolute constant $c_0$. Since $\sqrt T\log T=0$ at $T=1$, (3.8) is stated for $T\ge2$.
--   - The bound on $\mathrm{Reg}_T=\sup_u\mathrm{Reg}_T(u)$ is written as a bound for every comparator.
--   - The constants $M$ and $J$ may depend on $d$, $\mathcal A$, $\mathcal B$, the enumeration and $\theta$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 3.2, Theorem 3.1, p. 25 (proof in Appendix F, pp. 120–123)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Theorem 3.1 (Regret in the sharp action case).** Zhao–Tan, *Best-of-Both-Worlds FTRL for
Linear Bandits* (STOC submission version), Theorem 3.1, p.25: "For linear bandits with compact
action sets, GIA-FTRL guarantees (3.8) `Reg_T = O(d√T log T)` in the adversarial regime.
Simultaneously, if the linear bandit instance satisfies the sharpness condition in (1.3),
GIA-FTRL guarantees `Reg_T = O(c*_ctr(𝒜, θ) d log T + M_{𝒜,θ} + J^cor_θ √C log₊(C))` (3.10) in
the corrupted stochastic regime, where `M_{𝒜,θ}` and `J^cor_θ` are finite parameter-dependent
constants independent of `T, C`."

GIA-FTRL is run on a compact generator `ℬ` of the compact action set `𝒜 ⊆ 𝔹^d`
(`span 𝒜 = ℝ^d`, `k = dim aff 𝒦 ≥ 1`) with an enumeration `e` of `ℚ^d`. `Reg_T = sup_{u∈𝒜}
Reg_T(u)` is written as a bound for every comparator `u ∈ 𝒜`. `O(·)` is an absolute constant
`c₀`; (3.8) is stated for `T ≥ 2` (at `T = 1`, `√T log T = 0`). `log₊ x = log max{e, x}`. -/
theorem theorem_3_1 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d : ℕ}, 1 ≤ d → ∀ (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ),
      IsCompact 𝒜 → IsCompact ℬ → IsGenerator 𝒜 ℬ → (∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) →
      Submodule.span ℝ 𝒜 = ⊤ → 1 ≤ kdim ℬ → Function.Surjective e →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : GRun d Ω), 2 ≤ T → IsGIAFTRLRun P 𝒜 ℬ e T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤ c₀ * ((d : ℝ) * Real.sqrt T * Real.log T)) ∧
      (∀ (θ astar : Fin d → ℝ), setNorm 𝒜 θ ≤ 1 → astar ∈ 𝒜 →
        (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) → IsSharp 𝒜 θ astar →
        ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
          IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤
            c₀ * (cstarCtr 𝒜 θ astar * d * Real.log T) + M +
              J * Real.sqrt C * Real.log (max (Real.exp 1) C)) := by sorry

end IAFTRL
