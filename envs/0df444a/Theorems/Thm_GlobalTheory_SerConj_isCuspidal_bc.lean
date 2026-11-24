-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_isCuspidal_bc
-- name    : GlobalTheory.SerConj.isCuspidal_bc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:08.212243+00:00
-- url     : https://prove2.me/theorems/a15c6b3f-2bac-4c1a-b946-f0d70a82616d
-- title:
--   Ser Conj: is Cuspidal bc
-- statement:
--   The Ser Conj construction uses the is Cuspidal bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L110-L113

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

theorem GlobalTheory.SerConj.isCuspidal_bc (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) : IsCuspidal K (bc σ τ) := by sorry
