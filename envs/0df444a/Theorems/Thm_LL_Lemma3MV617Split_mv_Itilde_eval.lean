-- Prove2me | Theorems.Thm_LL_Lemma3MV617Split_mv_Itilde_eval
-- name    : LL_Lemma3MV617Split.mv_Itilde_eval
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T13:13:10.994101+00:00
-- url     : https://prove2.me/theorems/95b5137b-132d-577f-a02a-c3869e008598
-- title:
--   Orthogonality evaluation of $\int_0^1\tilde T(\eta)^2e(-m\eta)\,d\eta$
-- statement:
--   For all real $\beta$, $P\ge0$ and $X$, and every integer $m$ with $1\le m\le X$, $$\int_0^1\tilde T(\eta)^2\,e(-\eta m)\,d\eta=\tilde I(m),$$ the integral being the interval integral of a complex valued function and $\tilde I(m)$ viewed as a complex number.
-- source:
--   Montgomery and Vaughan, Acta Arith. 27, 1975, page 365, the evaluation of $\tilde I(n)$ defined on page 364; Brüdern and Perelli 1998, display 13.

import Mathlib
import Definitions.Def_LL_Lemma3MV617Split_eC
import Definitions.Def_LL_Lemma3MV617Split_Itilde
import Definitions.Def_LL_Lemma3MV617Split_Ttilde

open Real Finset Filter

namespace LL_Lemma3MV617Split
theorem mv_Itilde_eval : ∀ β P X : ℝ, 0 ≤ P → ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X →
    (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * m))) = ((Itilde β P m : ℝ) : ℂ) := by sorry
end LL_Lemma3MV617Split
