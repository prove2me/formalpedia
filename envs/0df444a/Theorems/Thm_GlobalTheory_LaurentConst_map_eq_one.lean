-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_map_eq_one
-- name    : GlobalTheory.LaurentConst.map_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:30.222979+00:00
-- url     : https://prove2.me/theorems/8fbad9e8-dbfb-40a3-92bf-f2243cf93fa8
-- title:
--   Laurent Const: map eq one
-- statement:
--   The Laurent Const construction uses the map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L172-L175

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
variable {t}

theorem GlobalTheory.LaurentConst.map_eq_one {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : R →+* A) : ρ t = 1 := by sorry
