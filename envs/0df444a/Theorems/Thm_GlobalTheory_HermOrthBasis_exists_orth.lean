-- Prove2me | Theorems.Thm_GlobalTheory_HermOrthBasis_exists_orth
-- name    : GlobalTheory.HermOrthBasis.exists_orth
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:40:14.152713+00:00
-- url     : https://prove2.me/theorems/7aee275c-fc72-586b-8697-4ed17604f4c1
-- title:
--   Herm Orth Basis: exists orth
-- statement:
--   The Herm Orth Basis construction uses the exists orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L151-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L151-L197

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

theorem GlobalTheory.HermOrthBasis.exists_orth [CharZero F] (hH : IsHermND L Hm) (k : ℕ) : ∀ (m : ℕ) (x : Fin m → Fin n → E),
    IsUnit (gramT L Hm x).det → m + k = n → ∃ w : Fin k → Fin n → E,
      Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧
      (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by sorry
