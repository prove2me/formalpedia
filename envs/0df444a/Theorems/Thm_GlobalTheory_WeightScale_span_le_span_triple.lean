-- Prove2me | Theorems.Thm_GlobalTheory_WeightScale_span_le_span_triple
-- name    : GlobalTheory.WeightScale.span_le_span_triple
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:44.10704+00:00
-- url     : https://prove2.me/theorems/91bf6a2c-cf71-58da-873c-595b10118d5e
-- title:
--   Weight Scale: span le span triple
-- statement:
--   The Weight Scale construction uses the span le span triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsUnimodularSolTriple.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsUnimodularSolTriple.lean#L43-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsUnimodularSolTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeightScale
variable {A B : Type*} [CommRing A] [CommRing B]

theorem GlobalTheory.WeightScale.span_le_span_triple {u : A} (hu : IsUnit u) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (triple u P)) := by sorry
