-- Prove2me | Theorems.Thm_GlobalTheory_SameZeroScheme_appLE_appLE
-- name    : GlobalTheory.SameZeroScheme.appLE_appLE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:42.892902+00:00
-- url     : https://prove2.me/theorems/67fcb11b-75d2-4c37-a395-f29ecde18d5c
-- title:
--   Same Zero Scheme: app LE app LE
-- statement:
--   The Same Zero Scheme construction uses the app LE app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsoLineBundleOfRegularPullbacksSameZeroScheme.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsoLineBundleOfRegularPullbacksSameZeroScheme.lean#L22-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroScheme
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

theorem GlobalTheory.SameZeroScheme.appLE_appLE {X Y T : Scheme.{0}} (t : T ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ t ⁻¹ᵁ V) (h'' : ⊤ ≤ (t ≫ f) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE V ⊤ h').hom ((f.appLE U V h).hom a) = ((t ≫ f).appLE U ⊤ h'').hom a := by sorry
