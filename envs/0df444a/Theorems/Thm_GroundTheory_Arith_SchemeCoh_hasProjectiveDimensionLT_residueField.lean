-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_residueField
-- name    : GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_residueField
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:52.570122+00:00
-- url     : https://prove2.me/theorems/9b9cf03e-77e6-4c97-ac99-2dbd7d1d3dbb
-- title:
--   Scheme Coh: has Projective Dimension LT residue Field
-- statement:
--   The Scheme Coh construction uses the has Projective Dimension LT residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean#L119-L129

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

theorem GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_residueField [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) :
    HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) := by sorry
