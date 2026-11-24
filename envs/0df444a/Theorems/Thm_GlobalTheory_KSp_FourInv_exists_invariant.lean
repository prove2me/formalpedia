-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_exists_invariant
-- name    : GlobalTheory.KSp.FourInv.exists_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:12.715925+00:00
-- url     : https://prove2.me/theorems/3dfa3488-1c7a-42c9-80e0-c9fcd71b5557
-- title:
--   Four Inv: exists invariant
-- statement:
--   The Four Inv construction uses the exists invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L54-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L54-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
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
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

theorem GlobalTheory.KSp.FourInv.exists_invariant [IsTopologicalAddGroup X] {f : X → ℂ} (hf : f ∈ SB X) :
    ∃ U ∈ 𝓝 (0 : X), ∀ M : AddSubgroup X, (M : Set X) ⊆ U → ∀ t ∈ M, ∀ x, f (x + t) = f x := by sorry
