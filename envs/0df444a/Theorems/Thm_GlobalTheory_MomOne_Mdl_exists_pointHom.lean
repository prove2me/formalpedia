-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Mdl_exists_pointHom
-- name    : GlobalTheory.MomOne.Mdl.exists_pointHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:59.998176+00:00
-- url     : https://prove2.me/theorems/95df0208-034f-4078-85e1-c6ded4ef3fa2
-- title:
--   Mdl: exists point Hom
-- statement:
--   The Mdl construction uses the exists point Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/RingHomPointBijective.lean#L75-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/RingHomPointBijective.lean#L75-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_RingHomPointBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MomOne
open PowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical

theorem GlobalTheory.MomOne.Mdl.exists_pointHom (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by sorry
