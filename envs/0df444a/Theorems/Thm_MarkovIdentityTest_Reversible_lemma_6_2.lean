-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_6_2
-- name    : MarkovIdentityTest.Reversible.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:01.570199+00:00
-- url     : https://prove2.me/theorems/a424ef09-57cb-463e-9f63-e4d033e7b32e
-- title:
--   Lemma 6.2 — spectral separation forces row loss or occupation energy: $\varepsilon\sum_iu_i\le 9\sum_iu_iH^2(P_i,Q_i)+2O_P(u)$
-- statement:
--   Let $P,Q$ be stochastic $n\times n$ matrices and $\varepsilon$ a real number with $\Delta(P,Q)\ge\varepsilon$. Then every $u\in\mathbb R^n_+$ satisfies
--   $$\varepsilon\sum_iu_i\le9\sum_iu_iH^2(P_i,Q_i)+2O_P(u),$$
--   where $O_P(u)=\tfrac12\sum_{i,j}(\sqrt{u_iP_{ij}}-\sqrt{u_jP_{ji}})^2$. Applied to the departure counts $u=N$ it says that a separated alternative leaves evidence either in the visited rows or in the occupation energy.
--
--   Differences from the source:
--
--   - generalization: P reversible (standing assumption of §6) → P, Q arbitrary stochastic matrices; reason: the proof never uses detailed balance (INSIGHTS I1); specializes to the printed lemma
--   - encoding: u ∈ ℝⁿ₊ → u : Fin n → ℝ with u ≥ 0; reason: notation only
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 32, Lemma 6.2

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Lemma 6.2 (Jia, p. 32 / PDF 34), for arbitrary stochastic `P` and `Q` (insight I1: the proof
never uses reversibility of `P`). -/
theorem lemma_6_2 {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : IsStochastic P)
    (hQ : IsStochastic Q) (ε : ℝ) (hε : ε ≤ discrepancy P Q) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) :
    ε * ∑ i, u i ≤ 9 * ∑ i, u i * hellingerSq (P i) (Q i) + 2 * occupationEnergy P u := by sorry

end MarkovIdentityTest.Reversible
