-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_mem_smul_top_iff_repr
-- name    : GlobalTheory.CNorm.mem_smul_top_iff_repr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:12.912513+00:00
-- url     : https://prove2.me/theorems/36f1d8c4-1189-47ee-84ad-e84c7f0ed67e
-- title:
--   CNorm: mem smul top iff repr
-- statement:
--   The CNorm construction uses the mem smul top iff repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsAdicCompleteSpanAlgebraMapOfFreeFinite.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsAdicCompleteSpanAlgebraMapOfFreeFinite.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by sorry
