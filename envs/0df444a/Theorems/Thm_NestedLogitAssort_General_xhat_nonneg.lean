-- Prove2me | Theorems.Thm_NestedLogitAssort_General_xhat_nonneg
-- name    : NestedLogitAssort.General.xhat_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:50:24.196914+00:00
-- url     : https://prove2.me/theorems/c905a594-1d3f-4579-8747-4d8045cefba4
-- title:
--   Proof of Theorem 11: the restricted optimum has $\hat x\ge0$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Assume all weights and revenues are nonnegative. For every nest $i$ let $\sigma_i$ be a permutation of $N$ and let $\mathcal C_i=\{N^k_{ij}:k\in N,\ j=0,\dots,k\}\cup\{\{j\}:j\in N\}$ be built from it. If $(\hat x,\hat y)$ is an optimal solution of the restricted linear program (4) with the candidate collections $\mathcal C_i$, then
--
--   $$
--   \hat x\ge0 .
--   $$
--
--   This is the first step of the proof of Theorem 11: it lets the later steps multiply the constraints by the factor $\beta\ge1$.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0, padding products with v_ij = 0, and v0 = 0) → hypotheses 0 ≤ v0, 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: σ_i lists the products of nest i by nondecreasing weight, the ordering r_i1 ≥ … ≥ r_in holds, and max_i γ_i > 1 → σ_i any permutation; no ordering of revenues and no γ̄ > 1 assumed; reason: the argument uses only that ∅ and the singletons are candidates and that the constraint values are nonnegative when x < 0; it specializes to the page
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: problems (3) and (4) are min-x linear programs with variables x and (y_i)_{i∈M} → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x), y : M → ℝ; reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: N^k_ij: "the first j products with the largest revenues" among the k lightest products → NK σ k j: the j smallest indices of Light σ k; reason: products are indexed in nonincreasing revenue order (p. 7), so this is a revenue order with ties broken by index; NK σ n j = N_ij as on p. 26
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), p. 46, via the proof of Theorem 10 (Appendix A.3), p. 45

import Mathlib
import Definitions.Def_NestedLogitAssort_General_IsOpt4
import Definitions.Def_NestedLogitAssort_General_CandGen

namespace NestedLogitAssort.General

/-- **The restricted optimum has `x̂ ≥ 0`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), p. 46 (unnumbered): "Following an argument similar
to the one at the beginning of the proof of Theorem 10, we have `x̂ ≥ 0`", referring to p. 45.

If `(x, y)` is an optimal solution of (4) with the candidate collection
`{N^k_{ij} : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}` of Theorem 11 in every nest, then `x ≥ 0`.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed),
`r_{ij} ≥ 0` (revenues; implicit in the paper, used by the argument on p. 45), `γ_i ≥ 0` (p. 7).
The listings `σ i` are arbitrary permutations: the claim does not need them to be weight orders. -/
theorem xhat_nonneg {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i)
    (σ : M → Equiv.Perm (Fin n)) (x : ℝ) (y : M → ℝ)
    (hopt : IsOpt4 I (fun i => CandGen (σ i)) x y) :
    0 ≤ x := by sorry

end NestedLogitAssort.General
