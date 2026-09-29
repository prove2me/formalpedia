-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_mem_unitaryGroup
-- name    : KobayashiMaskawa1973.kmMatrix_mem_unitaryGroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T18:23:02.78515+00:00
-- url     : https://prove2.me/theorems/78e938f9-3325-4bfe-a227-445a76bd859d
-- title:
--   The Kobayashi--Maskawa matrix of Eq. (13) is unitary
-- statement:
--   Equation (13) of the paper exhibits the $3\times3$ mixing matrix of the 6-plet model in the form (with $c_i=\cos\theta_i$, $s_i=\sin\theta_i$)
--   $$
--   K(\theta_1,\theta_2,\theta_3,\delta)=
--   \begin{pmatrix}
--   c_1 & -s_1c_3 & -s_1s_3\\
--   s_1c_2 & c_1c_2c_3-s_2s_3e^{i\delta} & c_1c_2s_3+s_2c_3e^{i\delta}\\
--   s_1s_2 & c_1s_2c_3+c_2s_3e^{i\delta} & c_1s_2s_3-c_2c_3e^{i\delta}
--   \end{pmatrix},
--   $$
--   presented there as an admissible expression for the unitary matrix appearing in the charged weak current of the six-quark scheme.
--
--   The milestone asserts that this expression is indeed unitary for all real $\theta_1,\theta_2,\theta_3$ and all real $\delta$:
--   $$K^{\dagger}K=KK^{\dagger}=I_3 .$$
--
--   The claim is the well-definedness half of the parametrization: it certifies that Eq. (13) does describe mixing matrices, complementing the exhaustiveness statement that every $3\times3$ unitary matrix can be brought to this form.
--
--   **Formalization Note** Unitarity is membership in `Matrix.unitaryGroup (Fin 3) ℂ`. The paper does not display a verification of unitarity; it is implicit in presenting Eq. (13) as an admissible form of the mixing matrix.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 657, Eq. (13) (unitarity is implicit: Eq. (13) is presented as an expression for the 3x3 unitary matrix of the charged weak current)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_mem_unitaryGroup (θ₁ θ₂ θ₃ δ : ℝ) :
    kmMatrix θ₁ θ₂ θ₃ δ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by sorry

end KobayashiMaskawa1973
