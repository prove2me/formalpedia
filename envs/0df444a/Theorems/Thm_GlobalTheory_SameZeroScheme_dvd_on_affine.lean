-- Prove2me | Theorems.Thm_GlobalTheory_SameZeroScheme_dvd_on_affine
-- name    : GlobalTheory.SameZeroScheme.dvd_on_affine
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:14.028998+00:00
-- url     : https://prove2.me/theorems/c34668f2-8ba5-4244-97c9-8d24312d6e56
-- title:
--   Same Zero Scheme: dvd on affine
-- statement:
--   The Same Zero Scheme construction uses the dvd on affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean#L42-L61

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

theorem GlobalTheory.SameZeroScheme.dvd_on_affine {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by sorry
