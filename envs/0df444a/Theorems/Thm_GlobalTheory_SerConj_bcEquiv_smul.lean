-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_bcEquiv_smul
-- name    : GlobalTheory.SerConj.bcEquiv_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:52.251841+00:00
-- url     : https://prove2.me/theorems/6d663de2-e98d-4a99-9629-2cf87d4438ba
-- title:
--   Ser Conj: bc Equiv smul
-- statement:
--   The Ser Conj construction uses the bc Equiv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L84-L88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]

theorem GlobalTheory.SerConj.bcEquiv_smul (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (a : ℂ) (v : τ) :
    bcEquiv σ τ (a • v) = σ a • bcEquiv σ τ v := by sorry
