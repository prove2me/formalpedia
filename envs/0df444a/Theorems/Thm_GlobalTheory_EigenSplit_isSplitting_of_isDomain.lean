-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isDomain
-- name    : GlobalTheory.EigenSplit.isSplitting_of_isDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:05.49234+00:00
-- url     : https://prove2.me/theorems/f3912a5b-723e-4737-b97c-f88587cb1ae0
-- title:
--   Eigen Split: is Splitting of is Domain
-- statement:
--   The Eigen Split construction uses the is Splitting of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L786-L793
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L786-L793

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
omit [DecidableEq ι]

theorem GlobalTheory.EigenSplit.isSplitting_of_isDomain {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
    (f : S →+* R) (hu : IsUnit (NumberField.discr E : R)) :
    IsSplitting fun i => f.comp (σ i) := by sorry
