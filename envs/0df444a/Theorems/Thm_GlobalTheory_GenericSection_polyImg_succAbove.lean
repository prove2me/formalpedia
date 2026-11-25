-- Prove2me | Theorems.Thm_GlobalTheory_GenericSection_polyImg_succAbove
-- name    : GlobalTheory.GenericSection.polyImg_succAbove
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:16.80148+00:00
-- url     : https://prove2.me/theorems/ea244e31-e655-4334-9b82-3b6620ba64ca
-- title:
--   Generic Section: poly Img succ Above
-- statement:
--   The Generic Section construction uses the poly Img succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PolyImgSuccAbove.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PolyImgSuccAbove.lean#L29-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
open GlobalTheory GlobalTheory.GenericSection
variable {F : Type} [Field F] {D N : ℕ}
open NumberField MvPolynomial
variable {F : Type} [Field F] {D N : ℕ}

theorem GlobalTheory.GenericSection.polyImg_succAbove (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) (k : Fin N) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0.succAbove k) = X (Sum.inr (i, k)) := by sorry
