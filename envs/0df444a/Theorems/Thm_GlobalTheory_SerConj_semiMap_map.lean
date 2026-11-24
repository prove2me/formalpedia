-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_semiMap_map
-- name    : GlobalTheory.SerConj.semiMap_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:33.341534+00:00
-- url     : https://prove2.me/theorems/c91f3278-48b1-4591-a152-b93f40b7f7dd
-- title:
--   Ser Conj: semi Map map
-- statement:
--   The Ser Conj construction uses the semi Map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L49-L57

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
variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem GlobalTheory.SerConj.semiMap_map (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (A : ∀ i, V i →ₗ[ℂ] V i) (B : ∀ i, W i →ₗ[ℂ] W i) (h : ∀ i v, j i (A i v) = B i (j i v))
    (x : PiTensorProduct ℂ V) :
    semiMap σ j hj (PiTensorProduct.map A x) = PiTensorProduct.map B (semiMap σ j hj x) := by sorry
