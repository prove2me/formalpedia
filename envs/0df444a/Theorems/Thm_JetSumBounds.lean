-- Prove2me | Theorems.Thm_JetSumBounds
-- name    : JetSumBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:12:43.000518+00:00
-- url     : https://prove2.me/theorems/1c650350-9993-41cb-bf64-530db3d56fb4
-- title:
--   Jet Sum Bounds: Jet Sum Bounds
-- statement:
--   BOUNDS FOR THE ORDER-`i` JET OF A SUM OF TWO MAPS.  Three clauses:
--
--   * (1) ADDITIVITY ON AN OPEN SET.  For `E₁, E₂` of class `C^∞` on an OPEN `U` and `x ∈ U`,
--     `D^i (E₁ + E₂) (x) = D^i E₁ x + D^i E₂ x`.  Mathlib carries this only as
--     `iteratedFDeriv_add_apply`, whose hypotheses are GLOBAL `ContDiff ℝ ⊤` on all of the plane;
--     here the maps are smooth only on `U` -- in the intended use they are derivative fields of
--     solutions, smooth nowhere else -- so the global form does not apply.  The open-set version has
--     to be routed through `iteratedFDerivWithin`, where `IsOpen.uniqueDiffOn` supplies the
--     unique-differentiability side condition and `iteratedFDerivWithin_of_isOpen` identifies the
--     within-jet with the ambient one at points of `U`.  That routing is the content of this clause
--     and the reason the node exists.
--   * (2) SUP BOUNDS ADD.  If each of two vectors has norm at most `q` and `2q ≤ Q`, their sum has
--     norm at most `Q`.
--   * (3) TWO-POINT BOUNDS ADD.  If `‖a₁ - b₁‖ ≤ q t` and `‖a₂ - b₂‖ ≤ q t` with `2q ≤ Q` and
--     `0 ≤ t`, then `‖(a₁ + a₂) - (b₁ + b₂)‖ ≤ Q t`.  The rearrangement
--     `(a₁+a₂) - (b₁+b₂) = (a₁-b₁) + (a₂-b₂)` is `sub_add_sub_comm`, not the triangle inequality,
--     and doing it by rewriting under a norm is expensive; done once here it is free at each use.
--
--   Clauses (2) and (3) are elementary, and they are bundled with (1) deliberately: a consumer
--   applying (1) to a jet of a sum always needs exactly one of them next, and getting both from the
--   same citation keeps the arithmetic out of a context where `nlinarith` would have to rediscover it
--   among dozens of unrelated hypotheses.  Each clause carries its own quantifiers, so the node has
--   no parameters at all.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetSumBounds.lean#L26-L64
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetSumBounds.lean#L26-L64

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetSumBounds
set_option autoImplicit false

theorem JetSumBounds :
    (∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
        IsOpen U → ∀ (i : ℕ) (E₁ E₂ : Plane → Z),
        ContDiffOn ℝ (⊤ : ℕ∞) E₁ U → ContDiffOn ℝ (⊤ : ℕ∞) E₂ U →
        ∀ x ∈ U, iteratedFDeriv ℝ i (fun z => E₁ z + E₂ z) x
          = iteratedFDeriv ℝ i E₁ x + iteratedFDeriv ℝ i E₂ x)
      ∧ (∀ (W : Type) [NormedAddCommGroup W] (a₁ a₂ : W) (q Q : ℝ),
          ‖a₁‖ ≤ q → ‖a₂‖ ≤ q → 2 * q ≤ Q → ‖a₁ + a₂‖ ≤ Q)
      ∧ (∀ (W : Type) [NormedAddCommGroup W] (a₁ a₂ b₁ b₂ : W) (q Q t : ℝ),
          ‖a₁ - b₁‖ ≤ q * t → ‖a₂ - b₂‖ ≤ q * t → 2 * q ≤ Q → 0 ≤ t →
          ‖(a₁ + a₂) - (b₁ + b₂)‖ ≤ Q * t) := by sorry
