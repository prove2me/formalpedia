-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_unitary_two_rephase_cabibbo
-- name    : KobayashiMaskawa1973.unitary_two_rephase_cabibbo
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:58:11.376724+00:00
-- url     : https://prove2.me/theorems/a9096342-23c3-436d-bc03-e40d6e9d7b8e
-- title:
--   Every $2\times2$ unitary mixing matrix is rephasing equivalent to a real rotation (Eq. 6)
-- statement:
--   In the quartet (four-quark) scheme the charged weak current is governed by a $2\times2$ unitary matrix $U$, entering the gauge-interaction term through $\Lambda_+$ of Eq. (5). Kobayashi and Maskawa state that "with an appropriate phase convention of the quartet field we can take $U$ as" the real rotation of Eq. (6).
--
--   Formally: for every $U$ in the unitary group $\mathrm U(2)$ there is a real angle $\theta$ and there are real phases $a_1,a_2,b_1,b_2$ such that
--   $$\operatorname{diag}(e^{ia_1},e^{ia_2})\;U\;\operatorname{diag}(e^{ib_1},e^{ib_2})=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}.$$
--
--   This is the phase-counting statement behind the paper's conclusion that, in the quartet model with $\mathcal L'=0$, the charged-current interaction can be made real and hence no $CP$ violation arises from it: a $2\times2$ unitary matrix has four real parameters, and the field-phase redefinitions remove all but one, the Cabibbo angle.
--
--   **Formalization Note** Unitarity is membership in `Matrix.unitaryGroup (Fin 2) ℂ`; the angle $\theta$ is an arbitrary real number and is not confined to a fundamental domain.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 654, Eq. (6) and the sentence 'With an appropriate phase convention of the quartet field we can take U as ...'

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem unitary_two_rephase_cabibbo (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ θ : ℝ, RephasingEquiv U (cabibboMatrix θ) := by sorry

end KobayashiMaskawa1973
