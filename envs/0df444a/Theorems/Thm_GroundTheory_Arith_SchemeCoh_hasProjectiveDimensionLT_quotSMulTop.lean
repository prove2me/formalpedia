-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_quotSMulTop
-- name    : GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:06.380047+00:00
-- url     : https://prove2.me/theorems/fbd6ea00-4daa-4460-8480-048ceae0bb1b
-- title:
--   Scheme Coh: has Projective Dimension LT quot SMul Top
-- statement:
--   The Scheme Coh construction uses the has Projective Dimension LT quot SMul Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L14-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L14-L68

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

theorem GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1) := by sorry
