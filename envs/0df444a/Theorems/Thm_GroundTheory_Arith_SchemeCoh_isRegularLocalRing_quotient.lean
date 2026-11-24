-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_quotient
-- name    : GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:21.220865+00:00
-- url     : https://prove2.me/theorems/b2e84d09-2bea-4469-9c20-78f158f172d3
-- title:
--   Scheme Coh: is Regular Local Ring quotient
-- statement:
--   The Scheme Coh construction uses the is Regular Local Ring quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L89-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L89-L111

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
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
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]

theorem GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by sorry
