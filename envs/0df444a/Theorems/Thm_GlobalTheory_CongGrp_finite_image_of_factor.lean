-- Prove2me | Theorems.Thm_GlobalTheory_CongGrp_finite_image_of_factor
-- name    : GlobalTheory.CongGrp.finite_image_of_factor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:19:06.435999+00:00
-- url     : https://prove2.me/theorems/e78b1472-ff54-5a06-a606-68fb8b70ecd0
-- title:
--   Cong Grp: finite image of factor
-- statement:
--   The Cong Grp construction uses the finite image of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbit.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbit.lean#L15-L24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongGrp

theorem GlobalTheory.CongGrp.finite_image_of_factor {α β γ : Type} (S : Set α) (f : α → β) (g : α → γ) [Finite β]
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y → g x = g y) : (g '' S).Finite := by sorry
