-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_xhat_nonneg
-- name    : NestedLogitAssort.PartialCapture.xhat_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:59.023694+00:00
-- url     : https://prove2.me/theorems/353e7ecb-6ee4-49d0-8c46-acc06f45b611
-- title:
--   Optimal value $\hat x$ of the restricted problem is nonnegative
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $\hat z_i(\epsilon)$ be the greedy solution of the continuous knapsack (11): among the products with $v_{ij}\le\epsilon$, fill the capacity $\epsilon$ in order of decreasing revenue, each product up to the fraction $1$; set $\hat S_i(\epsilon)=\{j : \hat z_{ij}(\epsilon)=1\}$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution of the linear program (4) with the candidate assortments $\{\hat S_i(\epsilon):\epsilon\in[0,\infty]\}\cup\{\{j\}:j\in N\}$ in nest $i$. Then
--
--   $$
--   \hat x\ge 0.
--   $$
--
--   This is the first step of the proof of Theorem 10; it allows the reduction of (3) to (10), which is valid for $x\ge 0$.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ > 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: ϵ_i ∈ [0, ∞] → Ŝ_i(ϵ) for real ϵ ≥ 0, plus N (Finset.univ) for ϵ = ∞; reason: with infinite capacity every product is eligible and fits, so Ŝ_i(∞) = N (which also equals Ŝ_i(∑_j v_ij))
--   - encoding: ẑ_i(ϵ_i): an optimal solution to (11) obtained by sorting by revenue and filling the knapsack → closed-form greedy zhat filling eligible products (v_ij ≤ ϵ) in index order; a zero-weight product gets 1; reason: products are already sorted by revenue (p. 7); ties are filled in index order, which is one solution obtained in this fashion
--   - encoding: problems (3) and (4) are min-x linear programs → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x); reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), p. 45 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_IsOpt4
import Definitions.Def_NestedLogitAssort_PartialCapture_Cand

namespace NestedLogitAssort.PartialCapture

/-- **The optimal value `x̂` of the restricted problem is nonnegative.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), p. 45 (unnumbered): "First, note that `x̂ ≥ 0`."

If `(x̂, ŷ)` is an optimal solution of problem (4) with the candidate collections
`{Ŝ_i(ϵ_i) : ϵ_i ∈ [0, ∞]} ∪ {{j} : j ∈ N}`, then `x̂ ≥ 0`.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem xhat_nonneg {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (Cand I) x y) :
    0 ≤ x := by sorry

end NestedLogitAssort.PartialCapture
