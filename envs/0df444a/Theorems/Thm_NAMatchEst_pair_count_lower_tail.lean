-- Prove2me | Theorems.Thm_NAMatchEst_pair_count_lower_tail
-- name    : NAMatchEst.pair_count_lower_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T00:23:49.403873+00:00
-- url     : https://prove2.me/theorems/2eb10072-8dc0-47fc-bbfc-e1e2ebb1ac19
-- title:
--   Lower tail for the number of sampled pairs across two Bernoulli vertex samples
-- statement:
--   Let $S^L,S^R\subseteq\{0,\dots,n-1\}$ be two independent Bernoulli vertex samples: every vertex is put in $S^L$ independently with probability $p^L$ and in $S^R$ independently with probability $p^R$, where $p^L,p^R\in[0,1]$. Let $(a_1,b_1),\dots,(a_m,b_m)$ be $m$ pairs of vertices such that the $a_i$ are pairwise distinct and the $b_i$ are pairwise distinct, and let
--   $$Z=\big|\{i : a_i\in S^L,\ b_i\in S^R\}\big|,\qquad \mathbb E[Z]=m\,p^Lp^R.$$
--   Then
--   $$\Pr\Big[Z\le\frac{m\,p^Lp^R}{4}\Big]\le\exp\Big(-\frac{m\,p^R}{7}\Big)+\exp\Big(-\frac{m\,p^Lp^R}{14}\Big).$$
--
--   This is the lower-tail estimate behind the completeness of the certified-edge test (Lemma 3.8) and of the small-scale edge test (Lemma 3.13): the pairs are the two orientations of the edges of a matching, so each vertex occurs at most once as a left and at most once as a right endpoint, and the indicators are independent once one conditions on $S^R$.
--
--   **Formalization Note** The joint law of $(S^L,S^R)$ is `(bernDist pL).prod (bernDist pR)` on `(Fin n → Bool) × (Fin n → Bool)`; the hypotheses $p^L,p^R\in[0,1]$ make the clamp in `bernDist` inactive.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation (STOC 2027 submission), proof of Lemma 3.8, p.25 (PDF 29) and proof of Lemma 3.13, p.29 (PDF 33): counting matching edges whose left endpoint lies in the sample S^L and right endpoint in S^R, and applying the Chernoff lower tail (Proposition 2.1).

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_NAMatchEst_bernDist

namespace NAMatchEst

theorem pair_count_lower_tail {n m : ℕ} (pL pR : ℝ) (hpL : 0 ≤ pL ∧ pL ≤ 1)
    (hpR : 0 ≤ pR ∧ pR ≤ 1) (a b : Fin m → Fin n) (ha : Function.Injective a)
    (hb : Function.Injective b) :
    (∑ ω, ((bernDist (n := n) pL).prod (bernDist (n := n) pR)).prob ω *
        if ((Finset.univ.filter fun i => ω.1 (a i) = true ∧ ω.2 (b i) = true).card : ℝ) ≤
          m * pL * pR / 4 then 1 else 0) ≤
      Real.exp (-(m * pR) / 7) + Real.exp (-(m * pL * pR) / 14) := by sorry

end NAMatchEst
