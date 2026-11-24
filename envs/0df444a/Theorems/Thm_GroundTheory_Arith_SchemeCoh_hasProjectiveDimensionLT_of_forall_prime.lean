-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_forall_prime
-- name    : GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_forall_prime
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:45.989583+00:00
-- url     : https://prove2.me/theorems/86690282-8b13-403e-bb93-f251aecdfaf0
-- title:
--   Scheme Coh: has Projective Dimension LT of forall prime
-- statement:
--   The Scheme Coh construction uses the has Projective Dimension LT of forall prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L84-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L84-L117

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
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
open IsLocalRing Ideal RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R]
open CategoryTheory Abelian

theorem GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_forall_prime [IsNoetherianRing R] (n : ℕ) (I : Ideal R)
    (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ q)) n)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by sorry
