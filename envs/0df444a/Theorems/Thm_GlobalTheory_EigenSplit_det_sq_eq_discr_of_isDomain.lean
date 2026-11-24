-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_isDomain
-- name    : GlobalTheory.EigenSplit.det_sq_eq_discr_of_isDomain
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:16.172161+00:00
-- url     : https://prove2.me/theorems/3b6d0518-f3c6-4450-b8f6-4b648817da57
-- title:
--   Eigen Split: det sq eq discr of is Domain
-- statement:
--   The Eigen Split construction uses the det sq eq discr of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L721-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L721-L742

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

theorem GlobalTheory.EigenSplit.det_sq_eq_discr_of_isDomain {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : S) := by sorry
