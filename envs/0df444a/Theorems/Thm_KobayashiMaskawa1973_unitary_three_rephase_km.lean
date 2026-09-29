-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_unitary_three_rephase_km
-- name    : KobayashiMaskawa1973.unitary_three_rephase_km
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T18:47:19.319177+00:00
-- url     : https://prove2.me/theorems/d0d2b5e0-b1be-4d63-b018-0ef8463e10bb
-- title:
--   Every $3\times3$ unitary mixing matrix has the Kobayashi--Maskawa form (Eq. 13)
-- statement:
--   For the 6-plet model the paper states that the charged weak current is governed by a $3\times3$ unitary matrix and that, since not all phases can be absorbed into the phase convention of the six fields, "we can take, for example, the following expression", namely Eq. (13).
--
--   Formally: for every $U\in\mathrm U(3)$ there are real numbers $\theta_1,\theta_2,\theta_3,\delta$ and real phases $a_1,a_2,a_3,b_1,b_2,b_3$ such that
--   $$\operatorname{diag}(e^{ia_1},e^{ia_2},e^{ia_3})\;U\;\operatorname{diag}(e^{ib_1},e^{ib_2},e^{ib_3})
--   = K(\theta_1,\theta_2,\theta_3,\delta),$$
--   with $K$ the matrix of Eq. (13).
--
--   This is the exhaustiveness half of the parametrization, and the quantitative form of the paper's phase counting for six quarks: after all available field-phase redefinitions, three angles and one phase remain, and it is that residual phase $\delta$ which makes $CP$ violation possible through interference among the current components.
--
--   **Formalization Note** The angles and the phase are arbitrary real numbers; no fundamental domain is imposed and no uniqueness is asserted.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 657, Eq. (13) and the surrounding sentences on the 6-plet model ('we cannot absorb all phases of matrix elements into the phase convention and can take, for example, the following expression')

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem unitary_three_rephase_km (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ θ₁ θ₂ θ₃ δ : ℝ, RephasingEquiv U (kmMatrix θ₁ θ₂ θ₃ δ) := by sorry

end KobayashiMaskawa1973
