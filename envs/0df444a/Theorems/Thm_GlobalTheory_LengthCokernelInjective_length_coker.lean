-- Prove2me | Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_coker
-- name    : GlobalTheory.LengthCokernelInjective.length_coker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:35.113285+00:00
-- url     : https://prove2.me/theorems/5fc3c2ed-a601-4a29-b672-a8ff57f5e919
-- title:
--   Length Cokernel Injective: length coker
-- statement:
--   The Length Cokernel Injective construction uses the length coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L74-L80

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

theorem GlobalTheory.LengthCokernelInjective.length_coker (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by sorry
