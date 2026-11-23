-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_map
-- name    : GlobalTheory.EigenSplit.det_sq_eq_discr_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:07.31097+00:00
-- url     : https://prove2.me/theorems/4c5721bb-b6d6-4252-bab8-6e495a5b8806
-- title:
--   Eigen Split: det sq eq discr map
-- statement:
--   The Eigen Split construction uses the det sq eq discr map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L683-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L683-L689

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

theorem GlobalTheory.EigenSplit.det_sq_eq_discr_map {σ : ι → 𝓞 E →+* R} {b : Module.Basis ι ℤ (𝓞 E)}
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    {R' : Type*} [CommRing R'] (f : R →+* R') :
    (Matrix.of fun i j => f.comp (σ i) (b j)).det ^ 2 = (NumberField.discr E : R') := by sorry
