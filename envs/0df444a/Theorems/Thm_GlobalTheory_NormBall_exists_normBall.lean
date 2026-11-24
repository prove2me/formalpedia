-- Prove2me | Theorems.Thm_GlobalTheory_NormBall_exists_normBall
-- name    : GlobalTheory.NormBall.exists_normBall
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:30.559678+00:00
-- url     : https://prove2.me/theorems/ed766923-61af-4de7-81bc-d1394e69562d
-- title:
--   Norm Ball: exists norm Ball
-- statement:
--   The Norm Ball construction uses the exists norm Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenNormClosedBallQuadratic.lean#L176-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenNormClosedBallQuadratic.lean#L176-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
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
open ValuativeRel
open GlobalTheory GlobalTheory.NormBall
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open MeasureTheory Matrix
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.NormBall.exists_normBall : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ _root_.GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by sorry
