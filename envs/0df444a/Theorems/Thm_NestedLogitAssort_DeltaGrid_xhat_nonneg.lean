-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_xhat_nonneg
-- name    : NestedLogitAssort.DeltaGrid.xhat_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:09:35.480109+00:00
-- url     : https://prove2.me/theorems/5529f929-1583-4e21-932f-a0c59aaf9a69
-- title:
--   Proof of Theorem 12: the restricted optimum has $\hat x\ge0$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight and $r_{ij}$ the revenue of product $j$ in nest $i$, $v_{i0}$ the weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Assume all weights and revenues are nonnegative. Let $\mathcal C_i$, $i\in M$, be any collections of candidate assortments with $\emptyset\in\mathcal C_i$ for every $i$. If $(\hat x,\hat y)$ is an optimal solution of the restricted linear program (4) with these collections, then
--
--   $$
--   \hat x\ge0 .
--   $$
--
--   This is the first step of the proof of Theorem 12, obtained "by using the same argument at the beginning of the proof of Theorem 10"; it lets the later steps multiply the constraints by the factors $\delta^{\bar\gamma+1}$ and $\delta^{2\bar\gamma+1}$.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof uses it (x̂ ≥ 0 via p. 45: the right sides are positive when x̂ < 0; inserting (35) into (34) on p. 53 multiplies a lower bound by ∑ r v; Proposition 15's proof, p. 52, uses positive objective coefficients). With negative revenues the assortment Ŝ_il usually does not exist (if Ĝ_il < 0, no S satisfies δ∑rv ≥ Ĝ_il ≥ ∑rv); no counterexample to the theorem was found otherwise
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0, padding products with v_ij = 0, and v0 = 0) → hypotheses 0 ≤ v0, 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: the collections {Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}, with r_i1 ≥ … ≥ r_in, γ̄ = max_i γ_i > 1 and δ > 1 → any collections C i with ∅ ∈ C i; no ordering of revenues, no γ̄ and no δ assumed; reason: the argument of p. 45 uses only that ∅ is a candidate and that the constraint values are nonnegative when x < 0; the grid collection contains ∅, so the statement specializes to the page
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: problems (3) and (4) are min-x linear programs with variables x and (y_i)_{i∈M} → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x), y : M → ℝ; reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 53, via the proof of Theorem 10 (Appendix A.3), p. 45

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsOpt4

namespace NestedLogitAssort.DeltaGrid

/-- **The optimum of the restricted problem (4) has `x̂ ≥ 0`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 53 (unnumbered): "By using the same argument at
the beginning of the proof of Theorem 10, it follows that x̂ ≥ 0", with that argument in the proof
of Theorem 10 (Appendix A.3), p. 45.

For nonnegative weights and revenues, `γ_i ≥ 0`, and any candidate collections `C i` that
contain the empty assortment, every optimal solution `(x, y)` of (4) has `x ≥ 0`.

**Formalization Note.** Stated for every candidate collection containing `∅`, not only for the
grid collection of Theorem 12 (which contains `∅` by definition). -/
theorem xhat_nonneg {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i)
    (C : M → Set (Finset (Fin n))) (hC : ∀ i, ∅ ∈ C i)
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I C x y) :
    0 ≤ x := by sorry

end NestedLogitAssort.DeltaGrid
