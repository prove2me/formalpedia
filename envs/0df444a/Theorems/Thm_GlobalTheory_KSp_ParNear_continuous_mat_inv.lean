-- Prove2me | Theorems.Thm_GlobalTheory_KSp_ParNear_continuous_mat_inv
-- name    : GlobalTheory.KSp.ParNear.continuous_mat_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:38.455935+00:00
-- url     : https://prove2.me/theorems/e147c183-ccb6-42a5-858d-43c58d329671
-- title:
--   Par Near: continuous mat inv
-- statement:
--   The Par Near construction uses the continuous mat inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L42-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarEventuallyEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFixedNearOneSiegelParabolic
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
open Filter Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.ParNear
variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]
variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]
variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

theorem GlobalTheory.KSp.ParNear.continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ := by sorry
