-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianMove_preserves_frameLattice_levels
-- name    : GlobalTheory.T.hermitianMove_preserves_frameLattice_levels
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:28.232774+00:00
-- url     : https://prove2.me/theorems/e8819124-0b34-413b-9e51-47e5df228536
-- title:
--   T: hermitian Move preserves frame Lattice levels
-- statement:
--   The T construction uses the hermitian Move preserves frame Lattice levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovePreservesFrameLatticeLevelsStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovePreservesFrameLatticeLevelsStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevels
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevelsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianMove_preserves_frameLattice_levels : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → S.IsTerm d Λ₁ ∧ ∀ y ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)), (y ∈ Λ → y ∈ Λ₁) ∧ (y ∈ S.M d Λ₁ ↔ y ∈ S.M d Λ) ∧ S.lev (S.fr d Λ₁) (S.fr' d Λ₁) y = S.lev (S.fr d Λ) (S.fr' d Λ) y := by sorry
