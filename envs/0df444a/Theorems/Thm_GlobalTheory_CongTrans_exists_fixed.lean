-- Prove2me | Theorems.Thm_GlobalTheory_CongTrans_exists_fixed
-- name    : GlobalTheory.CongTrans.exists_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:10.891097+00:00
-- url     : https://prove2.me/theorems/5489af5b-9a32-471a-9df1-9291b0715c40
-- title:
--   Cong Trans: exists fixed
-- statement:
--   The Cong Trans construction uses the exists fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruentOneMatricesTransitiveNearHermitian.lean#L173-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruentOneMatricesTransitiveNearHermitian.lean#L173-L224

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
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
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
variable [CharZero F] (L : LocE F E)

theorem GlobalTheory.CongTrans.exists_fixed {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E)
    (h0 : ∀ Y, IsIntM L Y → IsIntM L (T Y))
    (hT : ∀ (n : ℕ) Y W, IsIntM L Y → IsIntM L W → ∃ W', IsIntM L W' ∧
      T (Y + algebraMap F E ϖ ^ n • W) = T Y + algebraMap F E ϖ ^ (n + 1) • W') :
    ∃ Z, IsIntM L Z ∧ T Z = Z := by sorry
