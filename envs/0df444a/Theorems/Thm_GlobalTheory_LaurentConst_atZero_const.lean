-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_atZero_const
-- name    : GlobalTheory.LaurentConst.atZero_const
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:36.171021+00:00
-- url     : https://prove2.me/theorems/345e895c-7c27-4cc8-8768-b3253b2723dd
-- title:
--   Laurent Const: at Zero const
-- statement:
--   The Laurent Const construction uses the at Zero const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L69-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L69-L69

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

theorem GlobalTheory.LaurentConst.atZero_const (c : R) : atZero R (algebraMap R _ c) = HahnSeries.C c := by sorry
