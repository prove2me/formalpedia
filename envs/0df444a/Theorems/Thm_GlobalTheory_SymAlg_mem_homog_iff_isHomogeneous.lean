-- Prove2me | Theorems.Thm_GlobalTheory_SymAlg_mem_homog_iff_isHomogeneous
-- name    : GlobalTheory.SymAlg.mem_homog_iff_isHomogeneous
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:54.063475+00:00
-- url     : https://prove2.me/theorems/5f37e6f3-e544-5153-8d49-dcb4682ed36f
-- title:
--   Sym Alg: mem homog iff is Homogeneous
-- statement:
--   The Sym Alg construction uses the mem homog iff is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L96-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemHomogIffIsHomogeneous.lean#L96-L124

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

theorem GlobalTheory.SymAlg.mem_homog_iff_isHomogeneous {ι : Type*} (b : Basis ι R M) (d : ℕ)
    (x : SymmetricAlgebra R M) :
    x ∈ homog R M d ↔ (SymmetricAlgebra.equivMvPolynomial b x).IsHomogeneous d := by sorry
