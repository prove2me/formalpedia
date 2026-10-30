-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_lemma9_identity
-- name    : NestedLogitAssort.PartialCapture.lemma9_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:29.323995+00:00
-- url     : https://prove2.me/theorems/208bfba5-6efe-43a3-9678-2b460195cbcf
-- title:
--   Identity in the proof of Lemma 9: $\max_S V_i(S)^{\gamma_i}(R_i(S)-x)=\max_{\epsilon\ge0}(v_{i0}+\epsilon)^{\gamma_i}[K_i(\epsilon)/(v_{i0}+\epsilon)-x]$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $K_i(\epsilon)=\max\{\sum_{j\in N}r_{ij}v_{ij}z_j : \sum_{j\in N}v_{ij}z_j\le\epsilon,\ z\in\{0,1\}^n\}$ be the 0–1 knapsack value (9).
--
--   Then for every nest $i$ and every $x\ge 0$ the maximum on the right is attained and
--
--   $$
--   \max_{S\subseteq N}V_i(S)^{\gamma_i}\bigl(R_i(S)-x\bigr)=\max_{\epsilon\ge 0}\Bigl\{(v_{i0}+\epsilon)^{\gamma_i}\Bigl[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-x\Bigr]\Bigr\}.
--   $$
--
--   This identity is the content of Lemma 9: it rewrites the exponentially many constraints of the linear program (3) as one knapsack-parametrized constraint per nest.
--
--   **Formalization Note** The statement says that the left side (a maximum over the finitely many subsets of $N$) is the greatest element of the set of values of the right-hand objective over $\epsilon\ge 0$.
--
--   Differences from the source:
--   - encoding: max_{Si⊂N} … = max_{ϵi≥0} {…} → IsGreatest {val10 I i ϵ x | ϵ ≥ 0} (Finset.sup' over all S of T I i S x); reason: states that the right-hand maximum is attained and equals the left-hand maximum, which is the paper's identity
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ > 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: K_i(ϵ_i) and K̂_i(ϵ_i) as maxima (9), (11) → sSup of the set of objective values, z ∈ {0,1}^n as a Finset of products; reason: for ϵ ≥ 0 the sets are nonempty and bounded and the maxima are attained, so sSup is the maximum
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Lemma 9, p. 23 (unnumbered display)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_T
import Definitions.Def_NestedLogitAssort_PartialCapture_val10

namespace NestedLogitAssort.PartialCapture

/-- **The identity in the proof of Lemma 9.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Lemma 9, p. 23 (unnumbered): "the result follows if we can show that
`max_{S_i⊂N} V_i(S_i)^{γ_i}(R_i(S_i) − x) = max_{ϵ_i≥0} {(v_{i0} + ϵ_i)^{γ_i} [K_i(ϵ_i)/(v_{i0} + ϵ_i) − x]}`
for any `x ≥ 0`."

For every nest `i` and `x ≥ 0`, the maximum over `ϵ ≥ 0` of the right side is attained and equals
the maximum over all `S ⊆ N` of the left side: the latter is the greatest element of the set of
values of the former.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem lemma9_identity {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (i : M) (x : ℝ) (hx : 0 ≤ x) :
    IsGreatest {w : ℝ | ∃ ε : ℝ, 0 ≤ ε ∧ w = val10 I i ε x}
      (Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) => T I i S x)) := by sorry

end NestedLogitAssort.PartialCapture
