-- Prove2me | Theorems.Thm_GlobalTheory_HermOrthBasis_orth_basis_perp
-- name    : GlobalTheory.HermOrthBasis.orth_basis_perp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:36.161848+00:00
-- url     : https://prove2.me/theorems/8d5c765b-708d-4057-b9e1-00ec89ce5c5c
-- title:
--   Herm Orth Basis: orth basis perp
-- statement:
--   The Herm Orth Basis construction uses the orth basis perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L199-L202

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HermOrthBasis.orth_basis_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → m ≤ n ∧ IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) ∧ ∃ w : Fin (n - m) → Fin n → E, Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧ (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by sorry
