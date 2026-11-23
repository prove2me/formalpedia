-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_hom_ext
-- name    : GlobalTheory.LaurentConst.hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:15.651069+00:00
-- url     : https://prove2.me/theorems/3abd54ce-3942-4ba7-9dbe-0a3fb41f5a28
-- title:
--   Laurent Const: hom ext
-- statement:
--   The Laurent Const construction uses the hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L23-L27

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

theorem GlobalTheory.LaurentConst.hom_ext {A : Type} [CommRing A] {f g : AddMonoidAlgebra L ℤ →+* A}
    (h₀ : ∀ c, f (single 0 c) = g (single 0 c)) (h₁ : f (single 1 1) = g (single 1 1)) : f = g := by sorry
