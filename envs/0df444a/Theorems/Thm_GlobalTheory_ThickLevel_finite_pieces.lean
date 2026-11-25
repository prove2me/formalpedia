-- Prove2me | Theorems.Thm_GlobalTheory_ThickLevel_finite_pieces
-- name    : GlobalTheory.ThickLevel.finite_pieces
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:47:19.314012+00:00
-- url     : https://prove2.me/theorems/bb107e27-c186-4ff7-a585-9825d56ab6d4
-- title:
--   Thick Level: finite pieces
-- statement:
--   The Thick Level construction uses the finite pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L73-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
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
open GlobalTheory GlobalTheory.ThickLevel

theorem GlobalTheory.ThickLevel.finite_pieces {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {T : Set W} (hT : IsCO W0 T)
    (P : Set (Set W)) (c : ℝ) (hc : 0 < c) (h1 : ∀ p ∈ P, IsCO W0 p ∧ cont W0 p = c ∧ p ⊆ T)
    (h2 : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) : P.Finite := by sorry
