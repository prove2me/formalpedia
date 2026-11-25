-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_le_quotient_add_one
-- name    : GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_le_quotient_add_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:56.972796+00:00
-- url     : https://prove2.me/theorems/ab0f724c-71f6-4123-94a8-6c09ad62934c
-- title:
--   Scheme Coh: span Finrank maximal Ideal le quotient add one
-- statement:
--   The Scheme Coh construction uses the span Finrank maximal Ideal le quotient add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L153-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDLocalization.lean#L153-L183

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

theorem GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_le_quotient_add_one [IsLocalRing R] [IsNoetherianRing R]
    {x : R} [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by sorry
