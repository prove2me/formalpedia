-- Prove2me | Theorems.Thm_InventoryControl_pot_round_monotone
-- name    : InventoryControl.pot_round_monotone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:12:58.843998+00:00
-- url     : https://prove2.me/theorems/4ca75788-6a29-4c4e-8f83-4e8e35d4d563
-- title:
--   Rounding to the nearest power of two times $q$ is monotone and lands within a factor $\sqrt 2$
-- statement:
--   Fix a basic quantity $q > 0$ and round each positive $Q$ to $2^{m}q$ with $m$ the integer
--   nearest to $\log_2(Q/q)$. Then for positive $Q \le Q'$,
--
--   1. $m(Q) \le m(Q')$, so nested batch quantities round to nested powers of two, which is
--      Roundy's constraint (9.16) with $k_i = m_i - m_{i-1} \ge 0$;
--   2. $\frac{\sqrt 2}{2}\,Q \le 2^{m(Q)}q \le \sqrt 2\,Q$, the window of Eq. (7.5).
--
--   The first property is the one sentence of the book's proof that concerns the constraints:
--   because the relaxed solution satisfies (9.18), its rounding satisfies (9.16). The second is
--   what the powers-of-two analysis of Sect. 7.1 needs of the rounding, and it is why the cost
--   bounds of Propositions 7.1 and 7.2 apply to it.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 180, Sect. 9.2.2, Eq. (9.22) and the sentence after: 'Due to (9.18), we know that mi >= mi-1 and the batch quantities obtained must consequently satisfy (9.16)'; the factor sqrt 2 is Eq. (7.5) p. 123

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem pot_round_monotone (q Q Q' : ℝ) (hq : 0 < q) (hQ : 0 < Q) (hQ' : 0 < Q') (hle : Q ≤ Q') :
    potRound q Q ≤ potRound q Q'
      ∧ Real.sqrt 2 / 2 * Q ≤ (2 : ℝ) ^ potRound q Q * q
      ∧ (2 : ℝ) ^ potRound q Q * q ≤ Real.sqrt 2 * Q := by sorry

end InventoryControl
