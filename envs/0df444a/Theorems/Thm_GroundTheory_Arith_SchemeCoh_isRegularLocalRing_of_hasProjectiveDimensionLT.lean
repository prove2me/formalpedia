-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_of_hasProjectiveDimensionLT
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_of_hasProjectiveDimensionLT
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:54.669045+00:00
-- url     : https://prove2.me/theorems/99674133-4fbc-40a5-9767-ca359dc597fc
-- title:
--   Scheme Coh: is Regular Local Ring of has Projective Dimension LT
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring of has Projective Dimension LT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L187-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L187-L343

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
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_of_hasProjectiveDimensionLT [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1)) :
    IsRegularLocalRing R := by sorry
