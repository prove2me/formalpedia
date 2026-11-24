-- Prove2me | Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_coker_of_not_injective
-- name    : GlobalTheory.LengthCokernelInjective.length_coker_of_not_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:31.836024+00:00
-- url     : https://prove2.me/theorems/f8478622-5484-4aba-89c3-20397d6a4d4a
-- title:
--   Length Cokernel Injective: length coker of not injective
-- statement:
--   The Length Cokernel Injective construction uses the length coker of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L54-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCokerOfNotInjective.lean#L54-L72

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

theorem GlobalTheory.LengthCokernelInjective.length_coker_of_not_injective (f : M →ₗ[R] M) (hf : LinearMap.ker f ≠ ⊥) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by sorry
