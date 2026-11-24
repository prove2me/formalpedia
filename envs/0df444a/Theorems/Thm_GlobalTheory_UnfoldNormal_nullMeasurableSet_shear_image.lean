-- Prove2me | Theorems.Thm_GlobalTheory_UnfoldNormal_nullMeasurableSet_shear_image
-- name    : GlobalTheory.UnfoldNormal.nullMeasurableSet_shear_image
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:24.028228+00:00
-- url     : https://prove2.me/theorems/65d4a360-a5d9-4570-8bc4-9b937e18ce17
-- title:
--   Unfold Normal: null Measurable Set shear image
-- statement:
--   The Unfold Normal construction uses the null Measurable Set shear image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NullMeasurableSetShearImage.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NullMeasurableSetShearImage.lean#L51-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnfoldNormal
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

theorem GlobalTheory.UnfoldNormal.nullMeasurableSet_shear_image {N : Subgroup H} (hN : IsClosed (N : Set H)) (κ : Measure N)
    (ν : Measure H) {A : Set N} {B : Set H} (hA : NullMeasurableSet A κ) (hB : NullMeasurableSet B ν) :
    NullMeasurableSet (shear N '' (A ×ˢ B)) ((κ.prod ν).map (shear N)) := by sorry
