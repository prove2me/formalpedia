-- Prove2me | Theorems.Thm_GlobalTheory_HL_moves_split_by_target
-- name    : GlobalTheory.HL.moves_split_by_target
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:20.332111+00:00
-- url     : https://prove2.me/theorems/fbfda73d-a612-507e-80b2-4f7497a76ba8
-- title:
--   HL: moves split by target
-- statement:
--   The HL construction uses the moves split by target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplit.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermDoubleCosetMovesFiniteTargetsSplit.lean#L150-L163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplit
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

theorem GlobalTheory.HL.moves_split_by_target : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by sorry
