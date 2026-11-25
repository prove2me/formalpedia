-- Prove2me | Theorems.Thm_GlobalTheory_HL_kern_row_sum
-- name    : GlobalTheory.HL.kern_row_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:29.682522+00:00
-- url     : https://prove2.me/theorems/fa0d4cbd-3f0d-5af5-95e8-d06bce781bea
-- title:
--   HL: kern row sum
-- statement:
--   The HL construction uses the kern row sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetKernelRowSumNearOne.lean#L89-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetKernelRowSumNearOne.lean#L89-L182

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetKernelRowSumNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.kern_row_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by sorry
