-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_hermForm_cols
-- name    : GlobalTheory.RiemannRel.hermForm_cols
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:23:27.948395+00:00
-- url     : https://prove2.me/theorems/9dc4e30a-ced6-41f5-8965-f8af25ff1af8
-- title:
--   Riemann Rel: herm Form cols
-- statement:
--   The Riemann Rel construction uses the herm Form cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelPeriodOfSymplecticBasis.lean#L23-L26

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

theorem GlobalTheory.RiemannRel.hermForm_cols {h : ℕ} (Hm P Q : Matrix (Fin h) (Fin h) ℂ) (i j : Fin h) :
    (Pᵀ * Hm * Q.map star) i j = hermForm Hm (fun k => P k i) (fun k => Q k j) := by sorry
