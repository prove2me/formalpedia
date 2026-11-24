-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_compactOpen_normClosedBall_quadratic
-- name    : GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:34.142365+00:00
-- url     : https://prove2.me/theorems/59b48509-5344-4294-8d1d-a1df7c28938d
-- title:
--   T: exists compact Open norm Closed Ball quadratic
-- statement:
--   The T construction uses the exists compact Open norm Closed Ball quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenNormClosedBallQuadraticStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenNormClosedBallQuadraticStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadraticStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by sorry
