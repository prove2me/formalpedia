-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_algHom_mem_pow
-- name    : GlobalTheory.SymAlg.algHom_mem_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:01.529799+00:00
-- url     : https://prove2.me/theorems/292017c4-1269-41f0-b8b8-5dac4c897437
-- title:
--   Sym Alg: alg Hom mem pow
-- statement:
--   The Sym Alg construction uses the alg Hom mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L68-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

theorem GlobalTheory.SymAlg.algHom_mem_pow {A : Type*} [CommRing A] [Algebra R A]
    (φ : SymmetricAlgebra R M →ₐ[R] A) (P : Submodule R A)
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) ∈ P) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : φ x ∈ P ^ d := by sorry
