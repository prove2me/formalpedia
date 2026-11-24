-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoExp_tsum_qClass_eq
-- name    : GlobalTheory.HeckeTwoExp.tsum_qClass_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:14:28.217748+00:00
-- url     : https://prove2.me/theorems/1b7a5e9b-272f-416d-b1b4-d6b3572fcf91
-- title:
--   Hecke Two Exp: tsum q Class eq
-- statement:
--   The Hecke Two Exp construction uses the tsum q Class eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L99-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L99-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoExp.tsum_qClass_eq [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by sorry
