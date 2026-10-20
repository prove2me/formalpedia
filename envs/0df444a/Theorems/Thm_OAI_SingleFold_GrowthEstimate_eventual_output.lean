-- Prove2me | Theorems.Thm_OAI_SingleFold_GrowthEstimate_eventual_output
-- name    : OAI.SingleFold.GrowthEstimate.eventual_output
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:09:43.811031+00:00
-- url     : https://prove2.me/theorems/86f3425b-7262-45b3-85c7-a47bc963eb7f
-- title:
--   The output $W(k^2)$ grows between $\exp(\delta\log^2u)$ and $u^u$
-- statement:
--   Let $W:\mathbb{N}\to\mathbb{N}$ with $W(j)>0$, and $a,c\in\mathbb{R}$ with $|\log W(j)-aj^2|\le c$ for all $j\ge1$. Assume $a>0$ and $c\ge0$. Then there is $u_0\ge4$ such that for all $u\ge u_0$ and every bracket index $k\ge1$ of $u$ (i.e. $W(k)\le u+W(1)<W(k+1)$),
--   $$
--   \frac{(\log u)^2}{128\,a}<\log W(k^2)<u\log u .
--   $$
--
--   This is the growth condition required of the function $g$ in the exponentiation system. The map $u\mapsto W(k^2)$ grows faster than every polynomial yet slower than $u^u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean#L143-L175

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

theorem OAI.SingleFold.GrowthEstimate.eventual_output (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) :
    ∃ u₀ : ℕ, 4≤u₀ ∧ ∀ u≥u₀, ∀ k, 1≤k →
      W k≤u+W 1 ∧ u+W 1<W (k+1) →
      (1/(128*a))*(Real.log (u:ℝ))^2 < Real.log (W (k^2):ℝ) ∧
      Real.log (W (k^2):ℝ) < (u:ℝ)*Real.log (u:ℝ) := by sorry
