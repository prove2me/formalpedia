-- Prove2me | Theorems.Thm_HumanMachine_Alone_pbar_thresholds
-- name    : HumanMachine.Alone.pbar_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:09.643594+00:00
-- url     : https://prove2.me/theorems/1fb0ac9d-7136-4137-ae85-c113f3bd11b7
-- title:
--   Appendix A — interior candidate crosses zero and one at the prior thresholds
-- statement:
--   For any information cost $\lambda>0$ and any real prior parameter $\mu$, the interior algebraic expression $\bar p$ crosses the endpoints of the probability interval exactly at the thresholds of Theorem 1:
--
--   $$
--   \bar p\ge 1\iff\mu\ge\overline\mu,\qquad
--   \bar p\le 0\iff\mu\le\underline\mu.
--   $$
--
--   These equivalences identify when the interior expression leaves $[0,1]$ and hence where the closed form switches cases.
--
--   **Formalization Note** The equivalences are algebraic and hold for every real $\mu$; the decision problem itself uses a probability prior.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 32 (PDF p. 33), proof of Theorem 1, threshold-crossing sentences.

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Alone

theorem pbar_thresholds (lam : ℝ) (hlam : 0 < lam) :
    ∀ mu : ℝ, (1 ≤ pBar lam mu ↔ muHigh lam ≤ mu) ∧
      (pBar lam mu ≤ 0 ↔ mu ≤ muLow lam) := by sorry

end HumanMachine.Alone
