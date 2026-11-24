-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_main
-- name    : GlobalTheory.FrameBasic.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:24.07411+00:00
-- url     : https://prove2.me/theorems/72a02f3f-117d-4d8e-99d1-2ede2ac4277d
-- title:
--   Frame Basic: main
-- statement:
--   The Frame Basic construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L360-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L360-L361

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameBasic.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), LinearIndependent E (Sum.elim S.f S.f') ∧ IsCompl S.ME S.W0 ∧ (∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c) ∧ IsUnit (S.D (Fin.last (r + 1))) ∧ (∀ l, S.D l ≠ 0 → IsUnit (S.D l)) ∧ S.th ≠ 0 ∧ S.th ∈ 𝒪[F] ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.W0 = Submodule.span E (Set.range b) := by sorry
