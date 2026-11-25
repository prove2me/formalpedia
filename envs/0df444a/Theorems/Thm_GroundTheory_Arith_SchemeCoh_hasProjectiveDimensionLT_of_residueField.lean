-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_residueField
-- name    : GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_residueField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:45.287774+00:00
-- url     : https://prove2.me/theorems/8161f2dc-f917-4441-895e-cd88556d4308
-- title:
--   Scheme Coh: has Projective Dimension LT of residue Field
-- statement:
--   The Scheme Coh construction uses the has Projective Dimension LT of residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L133-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L133-L190

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
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_residueField [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by sorry
