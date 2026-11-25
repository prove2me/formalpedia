-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_conjugateHom
-- name    : GlobalTheory.EigenSplit.isSplitting_conjugateHom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:24.847989+00:00
-- url     : https://prove2.me/theorems/e1af2c8a-05d2-4bc1-8c00-695a346b7fef
-- title:
--   Eigen Split: is Splitting conjugate Hom
-- statement:
--   The Eigen Split construction uses the is Splitting conjugate Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L777-L782
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L777-L782

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

theorem GlobalTheory.EigenSplit.isSplitting_conjugateHom {L : Type*} [Field L] [Algebra (𝓞 L) R] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (hc : Fintype.card ι = Module.finrank ℚ E)
    (hu : IsUnit (NumberField.discr E : R)) : IsSplitting fun i => conjugateHom L R (φ i) := by sorry
