-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_lemma_3_4
-- name    : IIDMultiItem.TwoPoint.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:28.225557+00:00
-- url     : https://prove2.me/theorems/bae337da-5a6f-49e1-9b36-6464dc08fc92
-- title:
--   Lemma 3.4 (upper bound) — every DSIC, ex-post IR mechanism, randomized or not, has Rev(M) ≤ mb(1 − p^n) + E_S[c [ϕ_{c,e*}]_+]
-- statement:
--   Let $F=p\delta_a+q\delta_b$ with $0<a<b$, $0<p<1$, $q=1-p$. Every mechanism $M=(x,s)$ on the two-point type space that is feasible ($x_{ij}\in[0,1]$, (2.1)) and DSIC and ex-post IR (2.2), randomized or not, satisfies
--   $$\mathrm{Rev}(M)\ \le\ mb(1-p^n)+\mathbb E_S\big[c\,[\phi_{c,e^*}]_+\big],$$
--   where $c$ is the number of all-low items and $e^*$ the largest exclusive count at the profile $S$, and $\phi_{0,r}=0$.
--
--   This is the upper-bound half of Theorem 3.3; the competitor class is all randomized mechanisms (real allocation probabilities, real payments of any sign).
--
--   Differences from the source:
--   - encoding: types t ∈ supp(F)^m = {a, b}^m → types S : Finset (Fin m), the set of items valued high; reason: the identification the paper makes at the start of Section 3 (a bijection preserving values and probabilities)
--   - generalization: n, m ≥ 1 (§2.1: n buyers, items [m] for a positive integer m) → any n, m ∈ ℕ; reason: at n = 0 the revenue is 0 and the right side is c [ϕ_{c,0}]_+ ≥ 0; at m = 0 IR forces s ≤ 0 and the right side is 0; for n, m ≥ 1 it is the paper's statement
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 15 (PDF 17), Lemma 3.4

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Counts

namespace IIDMultiItem.TwoPoint

/-- Lemma 3.4 (upper bound). Every DSIC, ex-post IR mechanism `M`, randomized or not, satisfies
`Rev(M) ≤ m b (1 − p^n) + E_S[c [ϕ_{c,e*}]_+]`. -/
theorem lemma_3_4 (n m : ℕ) (a b p : ℝ) (ha : 0 < a) (hab : a < b) (hp0 : 0 < p) (hp1 : p < 1)
    (M : Mechanism (Finset (Fin m)) n m) (hM : M.Feasible) (hIC : M.DSIC_IR (twoPoint a b p m)) :
    M.Rev (twoPoint a b p m) ≤ revFormula a b p n m := by sorry

end IIDMultiItem.TwoPoint
