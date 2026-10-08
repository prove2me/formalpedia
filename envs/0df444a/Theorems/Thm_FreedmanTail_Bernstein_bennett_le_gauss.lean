-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_bennett_le_gauss
-- name    : FreedmanTail.Bernstein.bennett_le_gauss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:50.412668+00:00
-- url     : https://prove2.me/theorems/e1fa30b7-ffbc-4b6e-ad76-200fcc932c54
-- title:
--   Proof of (4.1) — (b/(a+b))^{a+b} e^a ≤ exp[−a²/(2(a+b))] for a, b > 0
-- statement:
--   For all real numbers $a>0$ and $b>0$,
--   $$\Bigl(\frac{b}{a+b}\Bigr)^{a+b}e^{a}\le\exp\Bigl[-\frac{a^{2}}{2(a+b)}\Bigr].$$
--
--   This is the second inequality of Theorem (4.1), which the paper leaves to "calculus": it converts the Bennett form of the bound into the Bernstein (Gaussian-type) form $\exp[-a^2/2(a+b)]$.
--
--   **Formalization Note** $(b/(a+b))^{a+b}$ is a real power of a number in $(0,1)$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 108 (PDF p. 9), proof of (4.1) Theorem: 'the second follows by calculus'

import Mathlib

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (4.1) Theorem, p. 108 ("the second follows by calculus"):
`(b/(a+b))^{a+b} e^a ≤ exp[−a²/(2(a+b))]` for positive `a, b` (real power). -/
theorem bennett_le_gauss (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by sorry

end FreedmanTail.Bernstein
