-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_A_1
-- name    : NonMarkovColorings.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:09:32.683694+00:00
-- url     : https://prove2.me/theorems/b3c4e32f-7ec5-4191-abd7-e13f3d4915e2
-- title:
--   Lemma A.1 — the recursion of Proposition 5.6: $\ell_j,\log m_j\le 3^j(C_{cp}^2+\log(200C_{cp})+2)$ and $m_{100C_{cp}}\le\exp(\exp(C_{cp}^2))$
-- statement:
--   Let $\gamma=\exp(-C_{cp}^2)$ and let $\ell_j,m_j$ be the sequences $\ell_0=2$, $m_0=1$, $\ell_{j+1}=2\ell_j+\log(200C_{cp}m_j/\gamma)/\log 24$, $m_{j+1}=(200C_{cp}/\gamma)m_j\exp(\ell_{j+1}/96)$. There is $C_0$ such that for every integer $C_{cp}\ge C_0$ and every $0\le j\le 100C_{cp}$,
--   $$\ell_j\le 3^j\big(C_{cp}^2+\log(200C_{cp})+2\big),\qquad \log m_j\le 3^j\big(C_{cp}^2+\log(200C_{cp})+2\big);$$
--   in particular $\ell_{100C_{cp}}\le\exp(O(C_{cp}))$ and $m_{100C_{cp}}\le\exp(\exp(C_{cp}^2))$. This is the computation behind the size bound $|\mathcal P|\le\exp(\exp(C_{cp}^2))$ in Proposition 5.6 and in $\mathrm{BC}$.
--
--   Differences from the source:
--   - reading: "C_cp sufficiently large" → ∃ C0 : ℕ, ∀ Ccp ≥ C0; reason: standard reading; C_cp is an integer since 100C_cp is an index
--   - reading: ℓ_{100C_cp} ≤ exp(O(C_cp)) → ∃ K : ℝ (before C_cp), ℓ_{100C_cp} ≤ exp(K · C_cp); reason: O(·) is an explicit constant independent of C_cp (§1.3)
--   - encoding: recursion for 0 ≤ j < 100C_cp → ellSeq, mSeq defined for every j; reason: only j ≤ 100C_cp is used
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 71, Lemma A.1

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_RecursionSeq

namespace NonMarkovColorings.Main

/-- Lemma A.1. With `γ = exp(−C_cp²)` and `C_cp` sufficiently large, for every
`0 ≤ j ≤ 100 C_cp`, `ℓ_j ≤ 3^j (C_cp² + log(200 C_cp) + 2)` and
`log m_j ≤ 3^j (C_cp² + log(200 C_cp) + 2)`; in particular `ℓ_{100 C_cp} ≤ exp(O(C_cp))`
(one constant `K` for all such `C_cp`) and `m_{100 C_cp} ≤ exp(exp(C_cp²))`. -/
theorem lemma_A_1 :
    ∃ C0 : ℕ, ∃ K : ℝ, ∀ Ccp : ℕ, C0 ≤ Ccp →
      (∀ j : ℕ, j ≤ 100 * Ccp →
        ellSeq Ccp (Real.exp (-(Ccp : ℝ) ^ 2)) j ≤
            3 ^ j * ((Ccp : ℝ) ^ 2 + Real.log (200 * (Ccp : ℝ)) + 2) ∧
          Real.log (mSeq Ccp (Real.exp (-(Ccp : ℝ) ^ 2)) j) ≤
            3 ^ j * ((Ccp : ℝ) ^ 2 + Real.log (200 * (Ccp : ℝ)) + 2)) ∧
      ellSeq Ccp (Real.exp (-(Ccp : ℝ) ^ 2)) (100 * Ccp) ≤ Real.exp (K * Ccp) ∧
      mSeq Ccp (Real.exp (-(Ccp : ℝ) ^ 2)) (100 * Ccp) ≤ Real.exp (Real.exp ((Ccp : ℝ) ^ 2)) := by sorry

end NonMarkovColorings.Main
