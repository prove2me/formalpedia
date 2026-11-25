-- Prove2me | Theorems.Thm_GlobalTheory_HL_DualInter_exists_primitive
-- name    : GlobalTheory.HL.DualInter.exists_primitive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:02.705882+00:00
-- url     : https://prove2.me/theorems/04e3e1e7-7ab2-4bf9-9bdf-2088f93ab7d2
-- title:
--   Dual Inter: exists primitive
-- statement:
--   The Dual Inter construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L102-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L102-L147

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

theorem GlobalTheory.HL.DualInter.exists_primitive [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {y : Fin n → E} (hy : ∀ s : E, s • y = 0 → s = 0) :
    ∃ t : E, IsUnit t ∧ t • y ∈ Λ ∧ ∃ c ∈ Λ, hf L Hm (t • y) c = 1 := by sorry
