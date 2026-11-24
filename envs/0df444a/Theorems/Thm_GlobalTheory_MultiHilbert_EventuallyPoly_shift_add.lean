-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_EventuallyPoly_shift_add
-- name    : GlobalTheory.MultiHilbert.EventuallyPoly.shift_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:36.001611+00:00
-- url     : https://prove2.me/theorems/8f54a824-5196-4627-92db-222fe6b27e93
-- title:
--   Eventually Poly: shift add
-- statement:
--   The Eventually Poly construction uses the shift add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L33-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}

theorem GlobalTheory.MultiHilbert.EventuallyPoly.shift_add {f : (Fin r → ℕ) → ℚ} (hf : EventuallyPoly f) (e : Fin r → ℕ) :
    EventuallyPoly (fun n => f (n + e)) := by sorry
