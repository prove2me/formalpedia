-- Prove2me | Theorems.Thm_IAFTRL_theorem_3_1_alloc
-- name    : IAFTRL.theorem_3_1_alloc
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:38:34.079745+00:00
-- url     : https://prove2.me/theorems/bb39441c-f30d-4ada-8130-b67ab3acf961
-- title:
--   Appendix F.1.1 — a fixed comparison allocation with $c^{n}_{\mathrm{ctr}}\le 2c^*_{\mathrm{ctr}}$
-- statement:
--   Let $\mathcal A\subseteq\mathbb B^d$ ($d\ge1$) be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$, and let $\mathcal B$ be a compact generator, so $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$. Let $\theta$ have a unique optimal action $a^*\in\mathcal A$, and suppose the instance is sharp (1.3).
--
--   Then there is a finite feasible centered sampling allocation $n^\circ$ on $\mathcal B$ with
--   $$
--   c^{n^\circ}_{\mathrm{ctr}}(\mathcal B,\theta)\le2\,c^*_{\mathrm{ctr}}(\mathcal B,\theta).
--   $$
--
--   This is the choice of the fixed comparison allocation in Appendix F.1.1.
--   - When $c^*_{\mathrm{ctr}}>0$, the allocation comes from the definition of the infimum, (F.2).
--   - When $c^*_{\mathrm{ctr}}=0$, the source constructs an exact zero-cost allocation, (F.3)–(F.8).
--
--   Together with Proposition 3.1 and Lemma J.10, it yields Theorem 3.1.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix F.1.1, (F.1)–(F.8), pp. 120–121

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **A fixed finite comparison sampling allocation (Appendix F.1.1).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Appendix F.1.1,
(F.1)–(F.8), pp.120–121: "`c*_ctr > 0 ⟹ ∃ n° ∈ N_θ : c^{n°}_ctr ≤ 2c*_ctr` (F.2) … Use `n° = n₀`
when `c*_ctr = 0`. In both cases, `c^{n°}_ctr ≤ 2c*_ctr`", applied on the physical generator `ℬ`.

For a compact generator `ℬ` of a compact action set `𝒜 ⊆ 𝔹^d` spanning `ℝ^d`, a unique optimal
action `a* ∈ 𝒜` under `θ`, and sharpness (1.3), there is a finite feasible centered sampling
allocation `n°` on `ℬ` with `c^{n°}_ctr(ℬ, θ) ≤ 2 c*_ctr(ℬ, θ)`. -/
theorem theorem_3_1_alloc {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (θ astar : Fin d → ℝ) (hastar : astar ∈ 𝒜)
    (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) (hsharp : IsSharp 𝒜 θ astar) :
    ∃ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n ∧
      ctrCost θ astar n ≤ 2 * cstarCtr ℬ θ astar := by sorry

end IAFTRL
