-- Prove2me | Theorems.Thm_GlobalTheory_HL_DualInter_dual_inter
-- name    : GlobalTheory.HL.DualInter.dual_inter
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:08:31.162118+00:00
-- url     : https://prove2.me/theorems/f6265db2-b9d5-473c-843f-e0d053927373
-- title:
--   Dual Inter: dual inter
-- statement:
--   The Dual Inter construction uses the dual inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L192-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L192-L242

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm}
variable [IsNonarchimedeanLocalField F]

theorem GlobalTheory.HL.DualInter.dual_inter : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by sorry
