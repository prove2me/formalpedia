-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_quotient_add_one_le
-- name    : GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_quotient_add_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:36.55336+00:00
-- url     : https://prove2.me/theorems/4e335c70-7986-448e-a020-2f31443ba0fb
-- title:
--   Scheme Coh: span Finrank maximal Ideal quotient add one le
-- statement:
--   The Scheme Coh construction uses the span Finrank maximal Ideal quotient add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L12-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularLocalDomain.lean#L12-L74

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

theorem GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by sorry
