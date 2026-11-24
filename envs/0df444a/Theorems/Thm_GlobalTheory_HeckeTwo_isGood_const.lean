-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_isGood_const
-- name    : GlobalTheory.HeckeTwo.isGood_const
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:57.524681+00:00
-- url     : https://prove2.me/theorems/4a97cfaa-a59b-4bfc-946e-e4ef2df882ab
-- title:
--   Hecke Two: is Good const
-- statement:
--   The Hecke Two construction uses the is Good const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly.lean#L25-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
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
open GlobalTheory GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.isGood_const (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane) :
    GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by sorry
