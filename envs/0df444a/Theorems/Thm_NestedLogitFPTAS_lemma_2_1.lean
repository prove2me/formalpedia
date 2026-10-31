-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_2_1
-- name    : NestedLogitFPTAS.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:27.094995+00:00
-- url     : https://prove2.me/theorems/056f5c7f-e70f-4d6e-acb6-34420f146af9
-- title:
--   Lemma 2.1, p.8 — a dual optimum is $\mathcal C$-feasible with the revenue of $S^*$
-- statement:
--   Let $S^*$ be a $\mathcal C$-feasible assortment and let $S$ be an optimal solution of the dual problem $F(1,\omega_{[1,M]}(S^*),\rho_{[1,M]}(S^*))$, that is, of minimum total cost among the assortments with the same $\omega$- and $\rho$-quantities as $S^*$. Then $S$ is $\mathcal C$-feasible and
--   $$
--   \mathcal R(S)=\mathcal R(S^*).
--   $$
--   This is the bridge from revenue maximization to the cost-minimizing dual that the dynamic program approximates.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
--   - generalization: S* a maximum-revenue C-feasible assortment → every C-feasible assortment S*; reason: the proof uses only C-feasibility, and the maximum-revenue assortment is one of them
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 2.1, p.8

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 2.1, p.8: an optimal solution `S` of the dual problem of a
`C`-feasible `S*` is `C`-feasible and has the revenue of `S*`.

**Formalization Note.** The paper fixes `S*` of maximum revenue; only its `C`-feasibility is needed,
so the statement is for every `C`-feasible `S*`. -/
theorem lemma_2_1 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {Sstar S : Finset (Fin n)}
    (hSstar : I.Feasible Sstar) (hS : I.IsDualOptimal Sstar S) :
    I.Feasible S ∧ I.R S = I.R Sstar := by sorry

end NestedLogitFPTAS
