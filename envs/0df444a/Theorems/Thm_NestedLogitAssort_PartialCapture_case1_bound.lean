-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_case1_bound
-- name    : NestedLogitAssort.PartialCapture.case1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:51:45.762924+00:00
-- url     : https://prove2.me/theorems/ad14cc5c-8d72-4de4-8ef6-8e9523607fc8
-- title:
--   Case 1 of the proof of Theorem 10: one fractional component, (26)–(28)
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $K_i(\epsilon)=\max\{\sum_{j\in N}r_{ij}v_{ij}z_j : \sum_{j\in N}v_{ij}z_j\le\epsilon,\ z\in\{0,1\}^n\}$ be the 0–1 knapsack value (9). Let $\hat z_i(\epsilon)$ be the greedy solution of the continuous knapsack (11): among the products with $v_{ij}\le\epsilon$, fill the capacity $\epsilon$ in order of decreasing revenue, each product up to the fraction $1$; set $\hat S_i(\epsilon)=\{j : \hat z_{ij}(\epsilon)=1\}$.
--
--   Let $x\ge 0$ and $\epsilon\ge 0$, and let $k$ be a product with $0<\hat z_{ik}(\epsilon)<1$. If a real number $y_i$ satisfies the constraints of (4) for the two assortments $\hat S_i(\epsilon)$ and $\{k\}$,
--
--   $$
--   y_i\ge V_i(\hat S_i(\epsilon))^{\gamma_i}\bigl(R_i(\hat S_i(\epsilon))-x\bigr),\qquad y_i\ge V_i(\{k\})^{\gamma_i}\bigl(R_i(\{k\})-x\bigr),
--   $$
--
--   then
--
--   $$
--   2y_i\ge(v_{i0}+\epsilon)^{\gamma_i}\Bigl[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-2x\Bigr].
--   $$
--
--   In the proof of Theorem 10 this is applied with $x=\hat x$, $y_i=\hat y_i$ and $\epsilon=\hat\epsilon_i$, the maximizer of the right side, and gives the inequality (28): $(2\hat x,2\hat y)$ satisfies the constraint of (10) for nest $i$.
--
--   Differences from the source:
--   - generalization: (28) at the maximizer ϵ̂_i of the right side of (10) at 2x̂, with x = x̂ and y_i = ŷ_i from an optimal solution of (4) → every ϵ ≥ 0, every x ≥ 0 and every y_i satisfying the two constraints of (4) for Ŝ_i(ϵ) and {k}; reason: the derivation (26)–(28) uses only these two constraints, x ≥ 0 and ϵ ≥ 0; at ϵ = ϵ̂_i, x = x̂, y_i = ŷ_i it is (28), since the optimal (x̂, ŷ) satisfies both constraints
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ > 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: ẑ_i(ϵ_i): an optimal solution to (11) obtained by sorting by revenue and filling the knapsack → closed-form greedy zhat filling eligible products (v_ij ≤ ϵ) in index order; a zero-weight product gets 1; reason: products are already sorted by revenue (p. 7); ties are filled in index order, which is one solution obtained in this fashion
--   - encoding: K_i(ϵ_i) and K̂_i(ϵ_i) as maxima (9), (11) → sSup of the set of objective values, z ∈ {0,1}^n as a Finset of products; reason: for ϵ ≥ 0 the sets are nonempty and bounded and the maxima are attained, so sSup is the maximum
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), eqs. (26)–(28), pp. 45–46

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_T
import Definitions.Def_NestedLogitAssort_PartialCapture_Shat
import Definitions.Def_NestedLogitAssort_PartialCapture_val10

namespace NestedLogitAssort.PartialCapture

/-- **Case 1 of the proof of Theorem 10: one fractional component, (26)–(28).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), eqs. (26)–(28), pp. 45–46.

Let `x ≥ 0`, `ϵ ≥ 0`, and let `k` be a fractional component of `ẑ_i(ϵ)`
(`0 < ẑ_{ik}(ϵ) < 1`). If `y_i` satisfies the constraints of (4) for the assortments `Ŝ_i(ϵ)` and
`{k}`, i.e. `y_i ≥ V_i(Ŝ_i(ϵ))^{γ_i}(R_i(Ŝ_i(ϵ)) − x)` and `y_i ≥ V_i({k})^{γ_i}(R_i({k}) − x)`, then
`2 y_i ≥ (v_{i0} + ϵ)^{γ_i}[K_i(ϵ)/(v_{i0} + ϵ) − 2x]`.

The paper applies this at `x = x̂`, `y_i = ŷ_i` and `ϵ = ϵ̂_i`, the maximizer of the right side of
(10) at `2x̂`; the statement here holds for every `ϵ ≥ 0` and every such `y_i`.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem case1_bound {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (i : M) (x : ℝ) (hx : 0 ≤ x) (ε : ℝ) (hε : 0 ≤ ε) (k : Fin n)
    (hk0 : 0 < zhat I i ε k) (hk1 : zhat I i ε k < 1) (yi : ℝ)
    (hyS : T I i (Shat I i ε) x ≤ yi) (hyk : T I i {k} x ≤ yi) :
    val10 I i ε (2 * x) ≤ 2 * yi := by sorry

end NestedLogitAssort.PartialCapture
