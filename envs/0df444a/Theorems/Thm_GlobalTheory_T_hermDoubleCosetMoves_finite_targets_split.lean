-- Prove2me | Theorems.Thm_GlobalTheory_T_hermDoubleCosetMoves_finite_targets_split
-- name    : GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:04:40.063533+00:00
-- url     : https://prove2.me/theorems/8ec79477-a8d3-4657-8a9d-16dc5fe13276
-- title:
--   T: herm Double Coset Moves finite targets split
-- statement:
--   The T construction uses the herm Double Coset Moves finite targets split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplitStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplitStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplitStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by sorry
