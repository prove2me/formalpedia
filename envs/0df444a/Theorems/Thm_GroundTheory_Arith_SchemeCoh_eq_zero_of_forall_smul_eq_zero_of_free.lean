-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_zero_of_forall_smul_eq_zero_of_free
-- name    : GroundTheory.Arith.SchemeCoh.eq_zero_of_forall_smul_eq_zero_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:16.397097+00:00
-- url     : https://prove2.me/theorems/cc1a54ef-5618-4f86-9569-5fce0fd524ae
-- title:
--   Scheme Coh: eq zero of forall smul eq zero of free
-- statement:
--   The Scheme Coh construction uses the eq zero of forall smul eq zero of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L70-L77

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem GroundTheory.Arith.SchemeCoh.eq_zero_of_forall_smul_eq_zero_of_free {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {a : R} (h : ∀ m : M, a • m = 0) : a = 0 := by sorry
