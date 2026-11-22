-- Prove2me | Theorems.Thm_NormalizedWeakGradient
-- name    : NormalizedWeakGradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:11.391933+00:00
-- url     : https://prove2.me/theorems/8a11061e-21b6-4226-ae5f-772012ca103e
-- title:
--   Normalized Weak Gradient: Normalized Weak Gradient
-- statement:
--   THE DISTRIBUTIONAL HALF OF AFFINE NORMALIZATION.  If `u` is `p`-harmonic on `Ω` with weak
--   gradient `g`, then on the rescaled domain `{x | x₀ + r • x ∈ Ω}` the normalized function
--   `x ↦ (u (x₀ + r • x) - c) / M` has `x ↦ (r / M) • g (x₀ + r • x)` as a weak gradient:
--
--   `∫ ((u(x₀ + r x) - c)/M) • Dφ = - ∫ φ • ((r/M) g(x₀ + r x))`  for every test function `φ`.
--
--   This is one of the bridge facts the blow-up layer needs, not a step of bookkeeping: the paper's
--   iteration rescales its solution at every stage, and a rescaled function is only a weak solution
--   of anything once its weak gradient has been identified.  The additive constant `c` is carried
--   because the iteration subtracts one (`w x y = (u(x + y/4) - u x)/M₀`), and it DISAPPEARS from the
--   conclusion -- which is the content of the proof's one genuinely analytic step: the mean of the
--   gradient of a compactly supported test function vanishes, so the `c` term integrates to zero.
--
--   The proof pushes the test function forward rather than pulling the solution back.  Given `φ`
--   admissible for the rescaled domain, `AffineTestFunctionPullback` makes `ψ := φ ∘ S` admissible
--   for `Ω` itself and supplies the chain rule `Dφ(x) = r • Dψ(x₀ + r • x)`; the weak-gradient
--   identity for `u` is then applied to `ψ`, and the affine change of variables for Lebesgue measure
--   transports the resulting integral back.  Both Jacobian factors `|r^(-n)|` appear on the two sides
--   and cancel, which is why no dimensional constant survives into the statement.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/NormalizedWeakGradient.lean#L27-L130
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/NormalizedWeakGradient.lean#L27-L130

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_PHigherOrder_NormalizedWeakGradient
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false

theorem NormalizedWeakGradient (p : ℝ) (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane)
    (x₀ : Plane) (r M c : ℝ) (hr : 0 < r) (h : IsPHarm p Ω u g) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ {x : Plane | x₀ + r • x ∈ Ω} →
      ∫ x in {x : Plane | x₀ + r • x ∈ Ω}, ((u (x₀ + r • x) - c) / M) • gradient φ x
        = - ∫ x in {x : Plane | x₀ + r • x ∈ Ω}, φ x • ((r / M) • g (x₀ + r • x)) := by sorry
