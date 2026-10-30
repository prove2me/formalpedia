-- Prove2me | Theorems.Thm_NestedLogitAssort_General_factor12_feasible
-- name    : NestedLogitAssort.General.factor12_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:11.427818+00:00
-- url     : https://prove2.me/theorems/58f79750-45d2-4831-b985-57c0bf9940d3
-- title:
--   Theorem 11: scaling the restricted optimum $(\hat x,\hat y)$ by $\beta$ of (12) gives a feasible point of (3)
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$ sorted so that $r_{i1}\ge\dots\ge r_{in}$; $v_{ij}$ is the preference weight of product $j$ in nest $i$, $v_{i0}$ that of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i\ge0$ the dissimilarity parameter of nest $i$. Write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$, with $R_i(\emptyset)=0$.
--
--   Assume all preference weights are nonnegative ($v_0,v_{i0},v_{ij}\ge0$; zero is allowed), all revenues are nonnegative, $\gamma_i\ge0$ for every nest, and $\bar\gamma=\max_{i\in M}\gamma_i>1$ (Section 6). For every nest $i$ let $\sigma_i$ list its products by nondecreasing preference weight, let $N^k_{ij}$ be the $j$ products with the largest revenues among the $k$ products with the smallest weights ($N^k_{i0}=\emptyset$), and let $M^f=\{i:v_{i0}=0\}$ and $M^p=\{i:v_{i0}>0\}$ be the fully- and partially-captured nests. Let
--
--   $$
--   \beta=\max_{i\in M^f,\,j=2,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ \max_{i\in M^p,\,j=1,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ 2 \tag{12}
--   $$
--
--   and assume its denominators are positive. Let $(\hat x,\hat y)$ be an optimal solution of the restricted linear program (4) whose candidate assortments for nest $i$ are
--
--   $$
--   \{N^k_{ij}:k\in N,\ j=0,\dots,k\}\cup\{\{j\}:j\in N\}.
--   $$
--
--   Then $(\beta\hat x,\beta\hat y)$ is a feasible solution of the linear program (3):
--
--   $$
--   v_0\,\beta\hat x\ge\sum_{i\in M}\beta\hat y_i,\qquad \beta\hat y_i\ge V_i(S)^{\gamma_i}\bigl(R_i(S)-\beta\hat x\bigr)\quad\text{for all }S\subseteq N,\ i\in M.
--   $$
--
--   Combined with the paper's Theorem 1, the best assortment assembled from these at most $1+n+n^2$ candidates per nest earns at least a fraction $1/\beta$ of the optimal expected revenue, for arbitrary dissimilarity parameters and no-purchase weights, where the assortment problem is NP-hard.
--
--   **Formalization Note** The statement covers any finite set of nests, any $n$ (including $0$), and zero weights.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 11 uses it (p. 45 via p. 46 for x̂ ≥ 0, Case 2 on p. 48, Case 3 on p. 49). Without it Theorem 11 fails: v0 = 0, two nests with v_10 = v_20 = 0, γ = (0.7, 1.5), one product each, r = (−0.956, −0.343), v = (0.536, 0) give β = 2, x̂ = −0.956, ŷ = 0, and the constraint for {1} in nest 1 fails at (βx̂, βŷ)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v_i0 = 0, padding products with v_ij = 0, and v0 = 0) → hypotheses 0 ≤ v0, 0 ≤ v_i0, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: N^k_ij is built from "the products with the k smallest preference weights" (p. 25), which is not unique when weights are tied → every listing σ_i of the products of nest i by nondecreasing weight (IsWeightOrder), one per nest, universally quantified; reason: covers every tie-break the paper could mean; with distinct weights there is exactly one such σ_i and the statement is the paper's
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ ≠ 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: problems (3) and (4) are min-x linear programs with variables x and (y_i)_{i∈M} → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x), y : M → ℝ; reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: N^k_ij: "the first j products with the largest revenues" among the k lightest products → NK σ k j: the j smallest indices of Light σ k; reason: products are indexed in nonincreasing revenue order (p. 7), so this is a revenue order with ties broken by index; NK σ n j = N_ij as on p. 26
--   - encoding: (12) divides by V_i(N_i,j−1) and tacitly assumes the ratios are defined → hypothesis hden: V_i(N_i,j−1) > 0 for every listed pair (i, j) of (12); reason: excludes exactly the instances where (12) is undefined or +∞ (a fully-captured nest with v_i1 = 0 and n ≥ 2); automatic for partially-captured nests; without it Lean's a/0 = 0 would shrink β
--   - encoding: products N = {1, …, n} with r_i1 ≥ … ≥ r_in, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; the ordering is Antitone (r i); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Theorem 11, p. 26 (factor (12), p. 26; N^k_ij, p. 25; standing assumption γ̄ > 1, Section 6, p. 25; proof in Appendix A.4, pp. 46–49)

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Feas3
import Definitions.Def_NestedLogitAssort_General_IsOpt4
import Definitions.Def_NestedLogitAssort_General_CandGen
import Definitions.Def_NestedLogitAssort_General_IsWeightOrder
import Definitions.Def_NestedLogitAssort_General_factor12

namespace NestedLogitAssort.General

/-- **Theorem 11 (performance guarantee (12) for general nests).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Theorem 11, p. 26: "Let `(x̂, ŷ)` be an optimal solution to problem (4) when we solve this
problem after replacing the collection of candidate assortments `{A_{it} : t ∈ T_i}` in the second
set of constraints with the assortments `{N^k_{ij} : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}`. Then,
using `β` to denote the expression in (12), `(β x̂, β ŷ)` is a feasible solution to problem (3)."

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof, pp. 45, 48, 49);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `max_i γ_i > 1` (Section 6
standing assumption, p. 25). `σ i` is any listing of the products of nest `i` by nondecreasing
weight (all tie-breaks of "the products with the `k` smallest preference weights", p. 25), and the
candidate collection of nest `i` is `CandGen (σ i)`. `hden` says that every denominator
`V_i(N_{i,j−1})` of (12) is positive, which is where (12) is defined and finite; it is automatic for
partially-captured nests and says `v_{i1} > 0` for a fully-captured nest when `n ≥ 2`. Any finite set
of nests and any `n` (including `0`) are allowed. -/
theorem factor12_feasible {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγbar : ∃ i, 1 < I.γ i)
    (σ : M → Equiv.Perm (Fin n)) (hσ : ∀ i, IsWeightOrder I i (σ i))
    (hden : ∀ i j, Listed I i j → 0 < V I i (NBR n (j - 1)))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGen (σ i)) x y) :
    Feas3 I (factor12 I * x) (fun i => factor12 I * y i) := by sorry

end NestedLogitAssort.General
