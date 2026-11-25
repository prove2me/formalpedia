-- Prove2me | Theorems.Thm_GlobalTheory_CongTrans_mem_congK_iff
-- name    : GlobalTheory.CongTrans.mem_congK_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:33.990818+00:00
-- url     : https://prove2.me/theorems/c42f1bb0-c5c0-5664-9cbc-cb8d9bfaab56
-- title:
--   Cong Trans: mem cong K iff
-- statement:
--   The Cong Trans construction uses the mem cong K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruentOneMatricesTransitiveNearHermitian.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruentOneMatricesTransitiveNearHermitian.lean#L69-L81

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
variable (L : LocE F E) {m : ℕ}

theorem GlobalTheory.CongTrans.mem_congK_iff (ϖ : 𝒪[F]) (i : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    A ∈ congK L ϖ m i ↔ ∃ N, IsIntM L N ∧ A = 1 + algebraMap F E ϖ ^ i • N := by sorry
