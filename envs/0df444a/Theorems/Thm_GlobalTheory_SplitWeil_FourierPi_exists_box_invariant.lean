-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_invariant
-- name    : GlobalTheory.SplitWeil.FourierPi.exists_box_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:22.193802+00:00
-- url     : https://prove2.me/theorems/3746ce69-a798-47c0-a884-ebab97af1710
-- title:
--   Fourier Pi: exists box invariant
-- statement:
--   The Fourier Pi construction uses the exists box invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierTransformInversionLocalFieldPi.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem GlobalTheory.SplitWeil.FourierPi.exists_box_invariant {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∀ t ∈ box n s, ∀ x, f (x + t) = f x := by sorry
