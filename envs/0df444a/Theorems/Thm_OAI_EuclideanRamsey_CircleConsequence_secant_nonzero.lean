-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_secant_nonzero
-- name    : OAI.EuclideanRamsey.CircleConsequence.secant_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:25:33.552381+00:00
-- url     : https://prove2.me/theorems/46ac5070-b76a-4fd6-88f1-1dbf9a33f0bd
-- title:
--   Three distinct points on a circle are not collinear
-- statement:
--   Let $x,y,z\in\mathbb R^2$ satisfy $|x-c|^2=|y-c|^2=|z-c|^2=R$ for some $c\in\mathbb R^2$ and $R\in\mathbb R$, and let $x,y,z$ be pairwise distinct. Then
--   $$
--   (y_0-x_0)(z_1-x_1)-(y_1-x_1)(z_0-x_0)\ne0 .
--   $$
--
--   A line meets a circle in at most two points, so no three distinct concyclic points are collinear.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleGeometry.lean#L27-L72

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle

open OAI OAI.EuclideanRamsey

theorem OAI.EuclideanRamsey.CircleConsequence.secant_nonzero
    (x₀ x₁ y₀ y₁ z₀ z₁ c₀ c₁ R : ℝ)
    (hx : (x₀-c₀)^2 + (x₁-c₁)^2 = R)
    (hy : (y₀-c₀)^2 + (y₁-c₁)^2 = R)
    (hz : (z₀-c₀)^2 + (z₁-c₁)^2 = R)
    (hxy : x₀ ≠ y₀ ∨ x₁ ≠ y₁)
    (hxz : x₀ ≠ z₀ ∨ x₁ ≠ z₁)
    (hyz : y₀ ≠ z₀ ∨ y₁ ≠ z₁) :
    (y₀-x₀)*(z₁-x₁) - (y₁-x₁)*(z₀-x₀) ≠ 0 := by sorry
