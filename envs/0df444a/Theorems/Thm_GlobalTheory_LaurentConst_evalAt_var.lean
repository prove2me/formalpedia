-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_evalAt_var
-- name    : GlobalTheory.LaurentConst.evalAt_var
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:39.103229+00:00
-- url     : https://prove2.me/theorems/7b4d09e4-4e49-40b9-baf0-018ab534de36
-- title:
--   Laurent Const: eval At var
-- statement:
--   The Laurent Const construction uses the eval At var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L65-L67

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

theorem GlobalTheory.LaurentConst.evalAt_var {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) :
    evalAt r u (var L : AddMonoidAlgebra L ℤ) = u := by sorry
