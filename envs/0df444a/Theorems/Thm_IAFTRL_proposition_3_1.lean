-- Prove2me | Theorems.Thm_IAFTRL_proposition_3_1
-- name    : IAFTRL.proposition_3_1
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:38:23.175842+00:00
-- url     : https://prove2.me/theorems/24bf8170-d82c-4c1d-9a48-9c6baab81821
-- title:
--   Proposition 3.1 — GIA-FTRL regret for every fixed centered sampling allocation
-- statement:
--   **Setting.** Let $\mathcal A\subseteq\mathbb B^d$ ($d\ge1$) be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$. GIA-FTRL (Algorithm 2) runs on a compact generator $\mathcal B$, meaning $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$, with $k=\dim\operatorname{aff}(\mathrm{Conv}\,\mathcal B)\ge1$ and a fixed enumeration of $\mathbb Q^d$. The regret against a comparator $u$ is $\mathrm{Reg}_T(u)=\mathbb E\big[\sum_{t\le T}(A_t-u)^\top\theta_t\big]$, and $\mathrm{Reg}_T=\sup_{u\in\mathcal A}\mathrm{Reg}_T(u)$. In the corrupted stochastic regime, $\theta_t=\theta+c_t$ with $\|\theta\|_{\mathcal A}\le1$ and $\sum_{t\le T}\|c_t\|_{\mathcal A}\le C$ almost surely, and $\theta$ has a unique optimal action $a^*\in\mathcal A$. All objects are those of the definition `IAFTRL_GIAFTRL`.
--
--   There is an absolute constant $c_0>0$ with the following two properties.
--
--   1. **Adversarial regime.** Every run of GIA-FTRL satisfies $\mathrm{Reg}_T(u)\le c_0\,d\sqrt T\log T$ for all $T\ge2$ and all $u\in\mathcal A$. This is (3.8).
--   2. **Corrupted stochastic regime.** If the instance is sharp (1.3), then there is a finite constant $J^{\mathrm{cor}}_\theta$ with the following property. For every finite feasible centered sampling allocation $n$ on the generator $\mathcal B$ (Definition 1.2 with $\mathcal B$ in place of $\mathcal A$), there is a finite constant $M_n$ such that, for all $T\ge1$, $C\ge0$ and $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le c_0\,c^n_{\mathrm{ctr}}(\mathcal B,\theta)\,d\log T+M_n+J^{\mathrm{cor}}_\theta\sqrt C\log_+(C). \tag{3.9}
--   $$
--   The constant $J^{\mathrm{cor}}_\theta$ does not depend on $T$, $C$ or $n$. The constant $M_n$ depends on the instance and on $n$, but not on $T$ or $C$.
--
--   Theorem 3.1 follows from this proposition by choosing a fixed allocation with $c^{n}_{\mathrm{ctr}}\le2c^*_{\mathrm{ctr}}$ (Appendix F.1.1) and using $c^*_{\mathrm{ctr}}(\mathcal B,\theta)=c^*_{\mathrm{ctr}}(\mathcal A,\theta)$ (Lemma J.10).
--
--   **Formalization Note.** As in Theorem 3.1: (3.8) is stated for $T\ge2$, $O(\cdot)$ is an absolute constant $c_0$, and the regret bound is written for every comparator. In the formal statement, $J$ is chosen before $n$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 3.2, Proposition 3.1, p. 25 (proof in Appendix G, pp. 123–190)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Proposition 3.1.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission
version), Proposition 3.1, p.25: "For linear bandits with compact action sets, GIA-FTRL guarantees
`Reg_T = O(d√T log T)` (3.8) in the adversarial regime. Simultaneously, if the linear bandit
instance satisfies the sharpness condition in (1.3), then for every feasible centered sampling
allocation `n` in (1.4) and an arbitrary generator `ℬ` of `𝒜`, GIA-FTRL guarantees
`Reg_T = O(c^n_ctr(ℬ, θ) d log T + M_n + J^cor_θ √C log₊(C))` (3.9) in the corrupted stochastic
regime, where `J^cor_θ` is a finite instance-dependent constant independent of `T, C, n`, and `M_n`
is a finite constant depending on the instance and the sampling allocation `n`, but independent of
`T` and `C`."

The setting is that of `theorem_3_1`; the allocation `n` is a finite feasible centered sampling
allocation on the generator `ℬ` (`IsCtrAlloc ℬ θ a* n`), and `J` is chosen before `n`. -/
theorem proposition_3_1 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d : ℕ}, 1 ≤ d → ∀ (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ),
      IsCompact 𝒜 → IsCompact ℬ → IsGenerator 𝒜 ℬ → (∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) →
      Submodule.span ℝ 𝒜 = ⊤ → 1 ≤ kdim ℬ → Function.Surjective e →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : GRun d Ω), 2 ≤ T → IsGIAFTRLRun P 𝒜 ℬ e T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤ c₀ * ((d : ℝ) * Real.sqrt T * Real.log T)) ∧
      (∀ (θ astar : Fin d → ℝ), setNorm 𝒜 θ ≤ 1 → astar ∈ 𝒜 →
        (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) → IsSharp 𝒜 θ astar →
        ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
          ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
            IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
            ∀ u ∈ 𝒜, gRegretVs P T R u ≤
              c₀ * (ctrCost θ astar n * d * Real.log T) + M +
                J * Real.sqrt C * Real.log (max (Real.exp 1) C)) := by sorry

end IAFTRL
