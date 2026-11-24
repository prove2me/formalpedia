-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_app_sub_eq_zero
-- name    : GlobalTheory.MulUnramified.app_sub_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:28.947837+00:00
-- url     : https://prove2.me/theorems/e59a0867-2137-48f4-9a76-4d3b7a361a3d
-- title:
--   Mul Unramified: app sub eq zero
-- statement:
--   The Mul Unramified construction uses the app sub eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L31-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified

theorem GlobalTheory.MulUnramified.app_sub_eq_zero {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (s : Γ(X, V)) :
    i.app W (f.appLE V W hf s - g.appLE V W hg s) = 0 := by sorry
