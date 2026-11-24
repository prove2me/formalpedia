-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_simple_bc
-- name    : GlobalTheory.SerConj.simple_bc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:35.983202+00:00
-- url     : https://prove2.me/theorems/8bcab4bd-0b6e-40e2-9cd3-c882a5e591af
-- title:
--   Ser Conj: simple bc
-- statement:
--   The Ser Conj construction uses the simple bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L102-L106

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

theorem GlobalTheory.SerConj.simple_bc [Fintype Γ] (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ Γ} (h : Simple τ) : Simple (bc σ τ) := by sorry
