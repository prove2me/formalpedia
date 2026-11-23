-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_evalAt_single
-- name    : GlobalTheory.LaurentConst.evalAt_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:59.362867+00:00
-- url     : https://prove2.me/theorems/a61e2fd0-1848-404e-9627-7a3c4e4597f5
-- title:
--   Laurent Const: eval At single
-- statement:
--   The Laurent Const construction uses the eval At single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L19-L21

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

theorem GlobalTheory.LaurentConst.evalAt_single {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) (n : ℤ) (c : L) :
    evalAt r u (single n c) = r c * ((u ^ n : Aˣ) : A) := by sorry
