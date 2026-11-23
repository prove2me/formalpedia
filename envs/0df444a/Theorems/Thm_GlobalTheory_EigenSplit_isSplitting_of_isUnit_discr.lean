-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isUnit_discr
-- name    : GlobalTheory.EigenSplit.isSplitting_of_isUnit_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:40.162692+00:00
-- url     : https://prove2.me/theorems/aaf798de-9b60-49a6-97de-b5a0ba617a67
-- title:
--   Eigen Split: is Splitting of is Unit discr
-- statement:
--   The Eigen Split construction uses the is Splitting of is Unit discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L765-L768
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L765-L768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.EigenSplit.isSplitting_of_isUnit_discr {σ : ι → 𝓞 E →+* R} (b : Module.Basis ι ℤ (𝓞 E))
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    (hu : IsUnit (NumberField.discr E : R)) : IsSplitting σ := by sorry
