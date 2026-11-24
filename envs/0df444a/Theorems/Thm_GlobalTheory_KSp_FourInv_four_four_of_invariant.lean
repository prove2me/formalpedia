-- Prove2me | Theorems.Thm_GlobalTheory_KSp_FourInv_four_four_of_invariant
-- name    : GlobalTheory.KSp.FourInv.four_four_of_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:05.554596+00:00
-- url     : https://prove2.me/theorems/498f7cf9-7316-410c-baf2-3ca739c3af8f
-- title:
--   Four Inv: four four of invariant
-- statement:
--   The Four Inv construction uses the four four of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L247-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean#L247-L254

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
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem GlobalTheory.KSp.FourInv.four_four_of_invariant (hX : Good X) (he : IsPair e) (M : AddSubgroup X) (hMc : IsCompact (M : Set X))
    (hMo : IsOpen (M : Set X)) : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, (∀ t ∈ M, ∀ x, φ (x + t) = φ x) →
      ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by sorry
