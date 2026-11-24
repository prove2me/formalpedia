-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_isConstituent_bc
-- name    : GlobalTheory.SerConj.isConstituent_bc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:49.0768+00:00
-- url     : https://prove2.me/theorems/237d69ec-c8f8-4cb7-b348-114183427e57
-- title:
--   Ser Conj: is Constituent bc
-- statement:
--   The Ser Conj construction uses the is Constituent bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L115-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L115-L149

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
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SerConj.isConstituent_bc (σ : ℂ ≃+* ℂ) {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    {τ : FDRep ℂ (GL ι K)} (h : IsConstituent τ (hcRep K b lam)) :
    IsConstituent (bc σ τ) (hcRep K b fun c => bc σ (lam c)) := by sorry
