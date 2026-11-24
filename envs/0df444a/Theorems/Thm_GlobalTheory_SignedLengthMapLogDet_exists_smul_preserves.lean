-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_exists_smul_preserves
-- name    : GlobalTheory.SignedLengthMapLogDet.exists_smul_preserves
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:31.923285+00:00
-- url     : https://prove2.me/theorems/1061e7b6-36d0-498f-818a-99a6da43b584
-- title:
--   Signed Length Map Log Det: exists smul preserves
-- statement:
--   The Signed Length Map Log Det construction uses the exists smul preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L145-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L145-L184

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.SignedLengthMapLogDet.exists_smul_preserves (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ A, r • g x ∈ A := by sorry
