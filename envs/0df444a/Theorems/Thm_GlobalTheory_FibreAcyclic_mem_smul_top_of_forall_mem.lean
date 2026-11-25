-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_mem_smul_top_of_forall_mem
-- name    : GlobalTheory.FibreAcyclic.mem_smul_top_of_forall_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:03.557866+00:00
-- url     : https://prove2.me/theorems/aa7aacbc-49be-4a34-a5de-1e41c3fa05d1
-- title:
--   Fibre Acyclic: mem smul top of forall mem
-- statement:
--   The Fibre Acyclic construction uses the mem smul top of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L136-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
omit [IsLocalRing R]

theorem GlobalTheory.FibreAcyclic.mem_smul_top_of_forall_mem (N : Ideal R) {F : Type} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (f : Module.Dual R F) (hf : ∀ x, f x ∈ N) : f ∈ N • (⊤ : Submodule R (Module.Dual R F)) := by sorry
