-- Prove2me | Theorems.Thm_GlobalTheory_HL_SameTrace_exists_isometry_of_same_trace
-- name    : GlobalTheory.HL.SameTrace.exists_isometry_of_same_trace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:36:33.650612+00:00
-- url     : https://prove2.me/theorems/f609dc05-0cf8-5773-b79e-db51c044782e
-- title:
--   Same Trace: exists isometry of same trace
-- statement:
--   The Same Trace construction uses the exists isometry of same trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfSameTrace.lean#L98-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfSameTrace.lean#L98-L208

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SameTrace
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem GlobalTheory.HL.SameTrace.exists_isometry_of_same_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ La Lb, IsSD L Hm La → IsSD L Hm Lb → ∀ (m : ℕ) (e : Fin m → Fin n → E), LinearIndependent E e → (∀ i j, hf L Hm (e i) (e j) = 0) → (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), x ∈ La ↔ x ∈ Lb) → ∃ g ∈ isomG L Hm, (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), g x = x) ∧ g • La = Lb := by sorry
