-- Prove2me | Theorems.Thm_GlobalTheory_EffCartierData_isGen_of_mul
-- name    : GlobalTheory.EffCartierData.isGen_of_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:51.714456+00:00
-- url     : https://prove2.me/theorems/7d4d94d2-1972-4347-9843-8b2c827bda97
-- title:
--   Eff Cartier Data: is Gen of mul
-- statement:
--   The Eff Cartier Data construction uses the is Gen of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L586-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/CoeNonzeroLocusCanonicalEqComplRange.lean#L586-L614

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)

theorem GlobalTheory.EffCartierData.isGen_of_mul {N L M : LB X} {a : L.Sec} {b : M.Sec} {c : N.Sec} (ha : IsRegularSec a)
    (hb : IsRegularSec b) (w : LB.Gen (LB.div (LB.div N L) M))
    (H : ∀ (i : N.ι) (j : L.ι) (k : M.ι) {W : X.Opens} (h : W ≤ N.U i ⊓ L.U j ⊓ M.U k),
      resG X (h.trans (inf_le_left.trans inf_le_left)) (c.f i) =
        (res h (w.s ((i, j), k)) : Γ(X, W)ˣ) *
          (resG X (h.trans (inf_le_left.trans inf_le_right)) (a.f j) *
            resG X (h.trans inf_le_right) (b.f k))) : w.IsGen := by sorry
