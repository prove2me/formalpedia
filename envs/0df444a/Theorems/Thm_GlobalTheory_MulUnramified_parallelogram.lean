-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_parallelogram
-- name    : GlobalTheory.MulUnramified.parallelogram
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:56.606668+00:00
-- url     : https://prove2.me/theorems/dcf759ce-2be8-47b5-9bfc-8d13c68e6088
-- title:
--   Mul Unramified: parallelogram
-- statement:
--   The Mul Unramified construction uses the parallelogram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L49-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L49-L85

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

theorem GlobalTheory.MulUnramified.parallelogram {T P X : Scheme.{0}} (p q : P ⟶ X)
    (hpq : ∀ (Z : Scheme.{0}) (u v : Z ⟶ P), u ≫ p = v ≫ p → u ≫ q = v ≫ q → u = v)
    (a b c d : T ⟶ P) (hap : a ≫ p = d ≫ p) (hbp : b ≫ p = c ≫ p)
    (haq : a ≫ q = c ≫ q) (hbq : b ≫ q = d ≫ q)
    {V : X.Opens} (hV : IsAffineOpen V) {V' : P.Opens} (hV' : IsAffineOpen V')
    {W : T.Opens} (hW : IsAffineOpen W) (hp : V' ≤ p ⁻¹ᵁ V) (hq : V' ≤ q ⁻¹ᵁ V)
    (ha : W ≤ a ⁻¹ᵁ V') (hb : W ≤ b ⁻¹ᵁ V') (hc : W ≤ c ⁻¹ᵁ V') (hd : W ≤ d ⁻¹ᵁ V')
    (h : ∀ s t, (a.appLE V' W ha s - c.appLE V' W hc s) *
      (b.appLE V' W hb t - c.appLE V' W hc t) = 0) (s : Γ(P, V')) :
    d.appLE V' W hd s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := by sorry
