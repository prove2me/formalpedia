-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_map_re_mul
-- name    : GlobalTheory.RiemannRel.map_re_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:23:40.821802+00:00
-- url     : https://prove2.me/theorems/17bc41b7-4e18-4dd5-8e99-6c9cc4c2b5ab
-- title:
--   Riemann Rel: map re mul
-- statement:
--   The Riemann Rel construction uses the map re mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel

theorem GlobalTheory.RiemannRel.map_re_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.re = P.map Complex.re * Q.map Complex.re - P.map Complex.im * Q.map Complex.im := by sorry
