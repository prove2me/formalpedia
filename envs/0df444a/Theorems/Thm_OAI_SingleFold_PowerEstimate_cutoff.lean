-- Prove2me | Theorems.Thm_OAI_SingleFold_PowerEstimate_cutoff
-- name    : OAI.SingleFold.PowerEstimate.cutoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:20:26.368412+00:00
-- url     : https://prove2.me/theorems/c193c38b-a1cd-4a33-881b-4cbbb3299978
-- title:
--   The Pell witnesses fit under the growth cutoff
-- statement:
--   For $\ell,u_0,b,n,c\in\mathbb{N}$ let $u=(c+1)^\ell(n+1)(b+1)+u_0$. Let $\delta>0$, $\ell\ge1$ with $3<\delta\ell\log2$, $u_0\ge4$, $b\ge2$, and take $c=b^n$. Then
--   $$
--   \log\bigl((2bu)^n\bigr)<\delta(\log u)^2 .
--   $$
--
--   Since $y_{n+1}(a)\le(2a)^n$, this shows the Pell values for $a=bu$ lie below $\exp(\delta(\log u)^2)$, hence below $g(u)$. So the bound $w_3<g(w_0)$ in the power system is satisfiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L50-L95

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
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power

open OAI OAI.SingleFold OAI.SingleFold.PowerEstimate

theorem OAI.SingleFold.PowerEstimate.cutoff {δ : ℝ} {ell u₀ b n : ℕ} (hδ : 0<δ) (hell : 1≤ell)
    (hell' : 3<δ*(ell:ℝ)*Real.log 2) (h₀ : 4≤u₀) (hb : 2≤b) :
    let u := input ell u₀ b n (b^n)
    Real.log (((2*(b*u))^n:ℕ):ℝ) < δ*(Real.log (u:ℝ))^2 := by sorry
