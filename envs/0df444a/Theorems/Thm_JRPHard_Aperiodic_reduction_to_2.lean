-- Prove2me | Theorems.Thm_JRPHard_Aperiodic_reduction_to_2
-- name    : JRPHard.Aperiodic.reduction_to_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:13.171247+00:00
-- url     : https://prove2.me/theorems/f254a9b5-2b88-4895-b74c-38a52470d1cc
-- title:
--   Proof of Lemma 1, p. 9 — with q₂ = M the instance reduces to problem (2): JRP(q₁, M) = EOQ_{K₂,H₂}(M) + JRP^red(q₁)
-- statement:
--   Let $M$ be an odd composite number and let $\mathrm{JRP}$ be the aperiodic objective of the instance of Lemma 1. For every positive integer $q_1$,
--   $$\mathrm{JRP}(q_1, M) = \mathrm{EOQ}_{K_2,H_2}(M) + \mathrm{JRP}^{\mathrm{red}}(q_1), \qquad \mathrm{JRP}^{\mathrm{red}}(q_1) = M(M-1)\left(\frac{1}{q_1} - \frac{1}{\mathrm{lcm}(q_1,M)}\right) + 4q_1 .$$
--
--   Once item 2 is fixed at $q_2 = M$, minimizing the two-item objective is therefore the same as minimizing the one-variable objective of problem (2) over $q_1 \in \mathbb Z^+$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 9, proof of Lemma 1, "Optimal replenishment cycle for item 1", first sentence; problem (2), p. 8

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting

namespace JRPHard.Aperiodic

theorem reduction_to_2 (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (q : ℕ) (hq : 0 < q) :
    lemma1Cost M q M = eoq2 M M + jrpRed M q := by sorry

end JRPHard.Aperiodic
