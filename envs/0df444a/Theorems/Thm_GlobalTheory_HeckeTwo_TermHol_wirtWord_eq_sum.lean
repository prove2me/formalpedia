-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermHol_wirtWord_eq_sum
-- name    : GlobalTheory.HeckeTwo.TermHol.wirtWord_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:07:47.176446+00:00
-- url     : https://prove2.me/theorems/3f9fa0b6-cbdc-4977-8846-fffd6d2ab12d
-- title:
--   Term Hol: wirt Word eq sum
-- statement:
--   The Term Hol construction uses the wirt Word eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeFourierTermWirtingerWordDifferentiableOn.lean#L19-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeFourierTermWirtingerWordDifferentiableOn.lean#L19-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtYStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiTransformHasDerivAtHoloStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeFourierTermWirtingerWordDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermHol
open Classical

theorem GlobalTheory.HeckeTwo.TermHol.wirtWord_eq_sum (F : Type) [Field F] [NumberField F] (b ν : F) (hb : b ≠ 0) (hJ : (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane))
    (w : List (Emb F × Bool)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (qf : ι → Emb F → ℕ), ∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F,
      wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z = ∑ i, c i * termQ σ b ν (qf i) z := by sorry
