-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_constantCoeff_scaleP
-- name    : GlobalTheory.LaurentConst.constantCoeff_scaleP
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:37.20825+00:00
-- url     : https://prove2.me/theorems/4b9d1b3d-1280-4d5c-ab26-dfe30e5acf7b
-- title:
--   Laurent Const: constant Coeff scale P
-- statement:
--   The Laurent Const construction uses the constant Coeff scale P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L163-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
variable (r : L →+* R) (t : Rˣ)

theorem GlobalTheory.LaurentConst.constantCoeff_scaleP : PowerSeries.constantCoeff.comp (scaleP r t) =
    r.comp PowerSeries.constantCoeff := by sorry
