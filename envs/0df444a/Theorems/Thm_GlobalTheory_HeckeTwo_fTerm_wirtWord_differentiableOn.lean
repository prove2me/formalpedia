-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_fTerm_wirtWord_differentiableOn
-- name    : GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:15.64855+00:00
-- url     : https://prove2.me/theorems/796e5c82-e857-4a72-8ad1-f767d943ff84
-- title:
--   Hecke Two: f Term wirt Word differentiable On
-- statement:
--   The Hecke Two construction uses the f Term wirt Word differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeFourierTermWirtingerWordDifferentiableOn.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeFourierTermWirtingerWordDifferentiableOn.lean#L54-L65

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
open GlobalTheory.HeckeTwo.TermHol

theorem GlobalTheory.HeckeTwo.fTerm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
  DifferentiableOn ℂ (fun σ => wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z) halfPlane := by sorry
