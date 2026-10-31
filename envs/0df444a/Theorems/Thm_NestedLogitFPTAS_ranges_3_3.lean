-- Prove2me | Theorems.Thm_NestedLogitFPTAS_ranges_3_3
-- name    : NestedLogitFPTAS.ranges_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:26.60792+00:00
-- url     : https://prove2.me/theorems/5d750a7e-3e88-4531-95ca-c842a492b803
-- title:
--   §3.3, pp.11–12 — ranges of $w_+(T)^{\gamma_k}$ and $\mathcal R_k(T)\,w_+(T)^{\gamma_k}$
-- statement:
--   For every $T\subseteq N_k$,
--   $$
--   w_+(T)^{\gamma_k}\in\big[(W^\downarrow)^{\gamma^+},(W^\uparrow)^{\gamma^+}\big]\cup\{0\},
--   $$
--   $$
--   \mathcal R_k(T)\cdot w_+(T)^{\gamma_k}\in\big[\pi_{\min}r_{\min}(W^\downarrow)^{\gamma^+},\ r_{\max}(W^\uparrow)^{\gamma^+}\big]\cup\{0\}.
--   $$
--   Precisely, both values are $0$ for $T=\emptyset$ and lie in the intervals for $T\neq\emptyset$. These ranges are what the grids discretize.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §3.3, pp.11–12

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), §3.3, pp.11–12, the two displayed ranges: for every `T ⊆ Nₖ`,
`w₊(T)^{γₖ} ∈ [W↓^{γ⁺}, W↑^{γ⁺}] ∪ {0}` and
`Rₖ(T)·w₊(T)^{γₖ} ∈ [π_min·r_min·W↓^{γ⁺}, r_max·W↑^{γ⁺}] ∪ {0}`.

**Formalization Note.** The value `0` occurs for `T = ∅`, and the intervals for `T ≠ ∅`. -/
theorem ranges_3_3 {n M : ℕ} (I : Instance n M) (hI : I.Standing) (k : Fin M)
    {T : Finset (Fin n)} (hT : T ⊆ I.nestSet k) :
    (T = ∅ → I.wplus k T ^ I.γ k = 0 ∧ I.Rnest k T * I.wplus k T ^ I.γ k = 0) ∧
    (T.Nonempty →
      (I.wDown ^ I.gammaPlus ≤ I.wplus k T ^ I.γ k ∧
        I.wplus k T ^ I.γ k ≤ I.wUp ^ I.gammaPlus) ∧
      (I.piMin * I.rMin * I.wDown ^ I.gammaPlus ≤ I.Rnest k T * I.wplus k T ^ I.γ k ∧
        I.Rnest k T * I.wplus k T ^ I.γ k ≤ I.rMax * I.wUp ^ I.gammaPlus)) := by sorry

end NestedLogitFPTAS
