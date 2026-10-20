-- Prove2me | Theorems.Thm_OAI_SingleFold_GrowthEstimate_bracket_log
-- name    : OAI.SingleFold.GrowthEstimate.bracket_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:09:04.848389+00:00
-- url     : https://prove2.me/theorems/4a3e441e-9446-4d8f-a4ba-e6d565407062
-- title:
--   Logarithmic size of the bracketed value
-- statement:
--   Let $W:\mathbb{N}\to\mathbb{N}$ with $W(j)>0$, and $a,c\in\mathbb{R}$ with $|\log W(j)-aj^2|\le c$ for all $j\ge1$. Assume $a>0$, $k\ge1$ and $W(k)\le u+W(1)<W(k+1)$. Then
--   $$
--   ak^2-c\le\log\bigl(u+W(1)\bigr)<4ak^2+c .
--   $$
--
--   So the bracket index $k$ of $u$ satisfies $ak^2\asymp\log u$. This relates the input size to the index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean#L66-L82

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
open Filter
open scoped Topology
variable {W : ℕ → ℕ} {a c : ℝ}

theorem OAI.SingleFold.GrowthEstimate.bracket_log {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      a*(k:ℝ)^2-c ≤ Real.log (u+W 1:ℕ) ∧
      Real.log (u+W 1:ℕ) < 4*a*(k:ℝ)^2+c := by sorry
