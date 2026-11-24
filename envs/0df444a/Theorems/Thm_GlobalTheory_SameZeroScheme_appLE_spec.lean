-- Prove2me | Theorems.Thm_GlobalTheory_SameZeroScheme_appLE_spec
-- name    : GlobalTheory.SameZeroScheme.appLE_spec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:43.353519+00:00
-- url     : https://prove2.me/theorems/0a3c8bd5-8025-4bee-97ce-c981fd207932
-- title:
--   Same Zero Scheme: app LE spec
-- statement:
--   The Same Zero Scheme construction uses the app LE spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean#L24-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean#L24-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
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
open GlobalTheory GlobalTheory.SameZeroScheme
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.SameZeroScheme.appLE_spec {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by sorry
