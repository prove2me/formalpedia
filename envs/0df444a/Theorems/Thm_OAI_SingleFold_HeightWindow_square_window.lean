-- Prove2me | Theorems.Thm_OAI_SingleFold_HeightWindow_square_window
-- name    : OAI.SingleFold.HeightWindow.square_window
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:10:24.279944+00:00
-- url     : https://prove2.me/theorems/5cd4b9ec-c804-4e38-b81e-b54c95e05ec0
-- title:
--   A multiplicative window detects $r=k^2$
-- statement:
--   Let $W:\mathbb{N}\to\mathbb{N}$ with $W(j)>0$, and $a,c\in\mathbb{R}$ with $|\log W(j)-aj^2|\le c$ for all $j\ge1$. Let $c\ge0$, $\kappa>0$ and $k,r\ge1$, with
--   $$
--   6c<\log\kappa<2a-6c .
--   $$
--   Then the two inequalities $W(2k)W(r)W(1)\le\kappa\,W(k)^2W(r+1)$ and $W(k)^2W(r+1)\le\kappa\,W(2k)W(r)W(1)$ hold together if and only if $r=k^2$.
--
--   The relation $r=k^2$ is thus expressed by polynomial inequalities among heights. This is how the square of the index is computed inside the representation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean#L233-L277

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

open OAI OAI.SingleFold

theorem OAI.SingleFold.HeightWindow.square_window {W : ℕ → ℕ} {a c : ℝ} {κ k r : ℕ}
    (hW : ∀ j, 0 < W j)
    (happrox : ∀ j, 1 ≤ j → |Real.log (W j : ℝ) - a * (j : ℝ) ^ 2| ≤ c)
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6 * c < Real.log κ)
    (h₂ : Real.log κ < 2 * a - 6 * c) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
      W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔ r = k ^ 2 := by sorry
