-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_symm_smul
-- name    : GlobalTheory.SerConj.symm_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:25.848233+00:00
-- url     : https://prove2.me/theorems/afc5f3bb-6653-422e-97c6-259196f332c8
-- title:
--   Ser Conj: symm smul
-- statement:
--   The Ser Conj construction uses the symm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L59-L63

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

theorem GlobalTheory.SerConj.symm_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (σ : ℂ ≃+* ℂ)
    (j : A ≃+ B) (hj : ∀ (a : ℂ) v, j (a • v) = σ a • j v) (a : ℂ) (w : B) :
    j.symm (a • w) = σ.symm a • j.symm w := by sorry
