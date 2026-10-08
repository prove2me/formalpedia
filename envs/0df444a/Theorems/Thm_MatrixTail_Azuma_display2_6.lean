-- Prove2me | Theorems.Thm_MatrixTail_Azuma_display2_6
-- name    : MatrixTail.Azuma.display2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:51.684857+00:00
-- url     : https://prove2.me/theorems/fbf0bf9c-b620-4b40-9917-310549eccda9
-- title:
--   Display (2.6) — Golden–Thompson inequality: tr e^{A+H} ≤ tr(e^A e^H)
-- statement:
--   Let $A$ and $H$ be self-adjoint (Hermitian) $d\times d$ complex matrices. The **Golden–Thompson inequality** states that
--   $$
--   \operatorname{tr} e^{A+H} \le \operatorname{tr}\big(e^{A} e^{H}\big).
--   $$
--
--   The matrix exponential does not turn sums into products, and this trace inequality is the limited substitute for that rule. In the paper it is cited from Bhatia, *Matrix Analysis*, Sec. IX.3, and it is the first step in the symmetrization lemma (Lemma 7.6) behind the matrix Azuma inequality. The analogous inequality for three matrices is false.
--
--   **Formalization Note** The exponentials are defined by the continuous functional calculus. The trace $\operatorname{tr}(e^Ae^H)$ is real for Hermitian $A, H$, and the statement compares its real part.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 8, §2.4, display (2.6) (cited from [Bha97, Sec. IX.3])

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Display (2.6), the Golden–Thompson inequality.** Tropp, *User-Friendly Tail Bounds for Sums of Random
Matrices*, arXiv:1004.4389v7, §2.4, p. 8: "The Golden–Thompson inequality [Bha97, Sec. IX.3] states that
`tr e^{A+H} ≤ tr(e^A e^H)` for all s.a. `A, H`." The paper cites it without proof; it is the first step of the
proof of Lemma 7.6 (p. 29).

**Formalization Note.** Complex Hermitian `d × d` matrices; `e^A` is `cfc Real.exp A` (`mexp`) and
`tr e^{A+H}` is the real part of the trace (`trExp`). The trace `tr(e^A e^H)` is real for Hermitian `A, H`
(it equals `tr(e^{A/2} e^H e^{A/2})`), so taking its real part loses nothing. -/
theorem display2_6 {d : ℕ} (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    trExp (A + H) ≤ (Matrix.trace (mexp A * mexp H)).re := by sorry

end MatrixTail.Azuma
