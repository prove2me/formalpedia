-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_feas3_iff_feas10
-- name    : NestedLogitAssort.PartialCapture.feas3_iff_feas10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:04.320613+00:00
-- url     : https://prove2.me/theorems/e71ce56c-0c51-4592-9af9-131a6b599751
-- title:
--   Problems (3) and (10) have the same feasible points with $x\ge 0$
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $K_i(\epsilon)=\max\{\sum_{j\in N}r_{ij}v_{ij}z_j : \sum_{j\in N}v_{ij}z_j\le\epsilon,\ z\in\{0,1\}^n\}$ be the 0–1 knapsack value (9).
--
--   Then for every $x\ge 0$ and every $y\in\mathbb R^M$, the pair $(x,y)$ is feasible for the linear program (3),
--
--   $$
--   v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge V_i(S)^{\gamma_i}\bigl(R_i(S)-x\bigr)\ \ \forall S\subseteq N,\ i\in M,
--   $$
--
--   if and only if it is feasible for problem (10),
--
--   $$
--   v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge(v_{i0}+\epsilon)^{\gamma_i}\Bigl[\frac{K_i(\epsilon)}{v_{i0}+\epsilon}-x\Bigr]\ \ \forall\epsilon\ge 0,\ i\in M.
--   $$
--
--   This is the form of the equivalence of (3) and (10) (Lemma 9) that the proof of Theorem 10 uses: to show that a point with $x\ge0$ is feasible for (3) it suffices to check (10).
--
--   Differences from the source:
--   - reading: 'problem (10) is equivalent to problem (3)' (p. 45, citing Lemma 9) → for every x ≥ 0 and every y, (x, y) is feasible for (3) iff it is feasible for (10); reason: Lemma 9's proof establishes exactly the constraint identity for x ≥ 0, and the proof of Theorem 10 uses the equivalence only to transfer feasibility of (2x̂, 2ŷ) with x̂ ≥ 0
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: V_i(S_i)^γi and R_i(S_i) with the interpretation R_i(∅) = 0 → Real.rpow (0^0 = 1, 0^γ = 0 for γ > 0) and division with a/0 = 0; reason: realizes R_i(∅) = 0; the 0^0 case (V_i(S) = 0 = γ_i) is not discussed by the paper and gets Lean's value 1
--   - encoding: y_i ≥ max_{ϵi≥0}{(v_i0 + ϵ_i)^γi [K_i(ϵ_i)/(v_i0 + ϵ_i) − x]} in (10) → Feas10: y_i ≥ val10 I i ϵ x for every ϵ ≥ 0; reason: identical whenever the maximum exists; avoids a junk sSup when the set is unbounded
--   - encoding: problems (3) and (4) are min-x linear programs → Feas3 (feasibility in (3)) and IsOpt4 (feasible for (4) and no feasible point has smaller x); reason: only feasibility in (3) and optimality in (4) enter the statement
--   - encoding: K_i(ϵ_i) and K̂_i(ϵ_i) as maxima (9), (11) → sSup of the set of objective values, z ∈ {0,1}^n as a Finset of products; reason: for ϵ ≥ 0 the sets are nonempty and bounded and the maxima are attained, so sSup is the maximum
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), p. 45 (unnumbered), via Lemma 9, p. 23

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Feas3
import Definitions.Def_NestedLogitAssort_PartialCapture_Feas10

namespace NestedLogitAssort.PartialCapture

/-- **Problems (3) and (10) have the same feasible points with `x ≥ 0`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 10 (Appendix A.3), p. 45 (unnumbered), via Lemma 9, p. 23: "Since problem
(10) is equivalent to problem (3), it is enough to show that `(2x̂, 2ŷ)` is a feasible solution to
problem (10)."

For every `x ≥ 0` and every `y`, `(x, y)` is feasible for (3) if and only if it is feasible for (10).

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem feas3_iff_feas10 {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (x : ℝ) (hx : 0 ≤ x) (y : M → ℝ) :
    Feas3 I x y ↔ Feas10 I x y := by sorry

end NestedLogitAssort.PartialCapture
