-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_isRegularLocalRing
-- name    : GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:57.377582+00:00
-- url     : https://prove2.me/theorems/2ef3b127-fff2-40bb-bd66-173c8bd43a7f
-- title:
--   Scheme Coh: has Projective Dimension LT of is Regular Local Ring
-- statement:
--   The Scheme Coh construction uses the has Projective Dimension LT of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L192-L195

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

theorem GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) := by sorry
