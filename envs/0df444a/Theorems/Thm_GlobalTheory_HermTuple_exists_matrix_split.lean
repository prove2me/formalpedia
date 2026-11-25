-- Prove2me | Theorems.Thm_GlobalTheory_HermTuple_exists_matrix_split
-- name    : GlobalTheory.HermTuple.exists_matrix_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:51.82075+00:00
-- url     : https://prove2.me/theorems/01fa4e1c-b176-4573-88b0-6ff8f3184a8f
-- title:
--   Herm Tuple: exists matrix split
-- statement:
--   The Herm Tuple construction uses the exists matrix split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEquivOfRetractions.lean#L118-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEquivOfRetractions.lean#L118-L177

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

theorem GlobalTheory.HermTuple.exists_matrix_split {K E n m : Type*} [Field K] [CommRing E]
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (c : E →+* E) (e : E ≃+* K × K) (he : ∀ x, e (c x) = (e x).swap)
    (G : Matrix n n E) (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) (X Y : Matrix n m E)
    (hu : IsUnit (Xᵀ * G * X.map c).det) (h : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : Matrix n n E, γᵀ * G * γ.map c = G ∧ γ * X = Y := by sorry
