-- Prove2me | Theorems.Thm_GlobalTheory_HermTuple_witt_tuples
-- name    : GlobalTheory.HermTuple.witt_tuples
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:38:23.215465+00:00
-- url     : https://prove2.me/theorems/7c7c0a96-9203-4670-b370-c2ae8af41251
-- title:
--   Herm Tuple: witt tuples
-- statement:
--   The Herm Tuple construction uses the witt tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEquivOfRetractions.lean#L299-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEquivOfRetractions.lean#L299-L367

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
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
open GlobalTheory GlobalTheory.HermTuple
open Matrix Module
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
open Matrix Module

theorem GlobalTheory.HermTuple.witt_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.HL.IsHermND L Hm → ∀ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i j, _root_.GlobalTheory.HL.hf L Hm (x i) (x j) = _root_.GlobalTheory.HL.hf L Hm (y i) (y j)) → IsUnit (Matrix.of fun i j => _root_.GlobalTheory.HL.hf L Hm (x i) (x j)).det → ∃ g ∈ _root_.GlobalTheory.HL.isomG L Hm, ∀ i, g (x i) = y i := by sorry
