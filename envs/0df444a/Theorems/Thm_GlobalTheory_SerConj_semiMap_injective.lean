-- Prove2me | Theorems.Thm_GlobalTheory_SerConj_semiMap_injective
-- name    : GlobalTheory.SerConj.semiMap_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:17.429348+00:00
-- url     : https://prove2.me/theorems/b00a5f66-bae7-46c7-bb4e-ccffc4b0f67a
-- title:
--   Ser Conj: semi Map injective
-- statement:
--   The Ser Conj construction uses the semi Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean#L65-L73

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

theorem GlobalTheory.SerConj.semiMap_injective (σ : ℂ ≃+* ℂ) (j : ∀ i, V i ≃+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    Function.Injective (semiMap σ.toRingHom (fun i => (j i).toAddMonoidHom) hj) := by sorry
