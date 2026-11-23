-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_comp_appLE_apply
-- name    : GlobalTheory.MulUnramified.comp_appLE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:21.882672+00:00
-- url     : https://prove2.me/theorems/0c55132c-2b15-48f5-afd5-891a33593c69
-- title:
--   Mul Unramified: comp app LE apply
-- statement:
--   The Mul Unramified construction uses the comp app LE apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L39-L43

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

theorem GlobalTheory.MulUnramified.comp_appLE_apply {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X) {x : T ⟶ X} (h : a ≫ p = x)
    (V : X.Opens) (V' : P.Opens) (W : T.Opens) (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V')
    (h₃ : W ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) :
    a.appLE V' W h₂ (p.appLE V V' h₁ s) = x.appLE V W h₃ s := by sorry
