-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_unitary
-- name    : KobayashiMaskawa1973.kmMatrix_unitary
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:12:56.688058+00:00
-- url     : https://prove2.me/theorems/afa9511f-d9aa-4ed5-b4a2-111d25d7c245
-- title:
--   Kobayashi--Maskawa mixing matrix is unitary
-- statement:
--   For all real angles $\theta_1, \theta_2, \theta_3 \in \mathbb{R}$ and real phase $\delta \in \mathbb{R}$, the Kobayashi--Maskawa mixing matrix
--
--   $$K(\theta_1, \theta_2, \theta_3, \delta) = \begin{pmatrix} c_1 & -s_1 c_3 & -s_1 s_3 \\ s_1 c_2 & c_1 c_2 c_3 - s_2 s_3 e^{i\delta} & c_1 c_2 s_3 + s_2 c_3 e^{i\delta} \\ s_1 s_2 & c_1 s_2 c_3 + c_2 s_3 e^{i\delta} & c_1 s_2 s_3 - c_2 c_3 e^{i\delta} \end{pmatrix}$$
--
--   (with $c_i = \cos \theta_i$, $s_i = \sin \theta_i$, and $e^{i\delta} = \exp(i\delta)$) is an element of the unitary group $\mathrm{U}(3)$.
--
--   This is Eq. (13) of Kobayashi and Maskawa (1973), expressing the general $3 \times 3$ unitary mixing matrix in the standard parameterization with three rotation angles and one complex phase.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_unitary (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by sorry

end KobayashiMaskawa1973
