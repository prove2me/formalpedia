-- Prove2me | Theorems.Thm_GlobalTheory_LengthCokernelInjective_relLength_map_eq_addVal_det
-- name    : GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:10.938803+00:00
-- url     : https://prove2.me/theorems/a28001db-f6df-48d2-b6a0-b084e315ea5c
-- title:
--   Length Cokernel Injective: rel Length map eq add Val det
-- statement:
--   The Length Cokernel Injective construction uses the rel Length map eq add Val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L82-L94

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {A : Submodule R V}
    [Module.Free R A] [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    GlobalTheory.relLength A (Submodule.map g A) =
      IsDiscreteValuationRing.addVal R (LinearMap.det (LinearMap.restrict g hg)) := by sorry
