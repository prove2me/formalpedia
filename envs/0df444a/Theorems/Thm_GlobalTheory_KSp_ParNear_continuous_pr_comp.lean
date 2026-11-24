-- Prove2me | Theorems.Thm_GlobalTheory_KSp_ParNear_continuous_pr_comp
-- name    : GlobalTheory.KSp.ParNear.continuous_pr_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:39.694582+00:00
-- url     : https://prove2.me/theorems/fea58027-93bd-4ae7-b371-150294df6658
-- title:
--   Par Near: continuous pr comp
-- statement:
--   The Par Near construction uses the continuous pr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L58-L62

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

theorem GlobalTheory.KSp.ParNear.continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by sorry
