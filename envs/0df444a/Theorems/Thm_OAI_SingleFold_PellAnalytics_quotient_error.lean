-- Prove2me | Theorems.Thm_OAI_SingleFold_PellAnalytics_quotient_error
-- name    : OAI.SingleFold.PellAnalytics.quotient_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:16:05.73633+00:00
-- url     : https://prove2.me/theorems/41f6d4bf-c72f-40a6-a6a7-34e77be0415d
-- title:
--   The Pell quotient lies within $1$ of $b^n$
-- statement:
--   Let $b,n,c,u\in\mathbb{N}$ with $(c+1)(n+1)+4\le u$ and $b^n\le c$, and let $F,H$ be reals with $H>0$ and
--   $$
--   b^n\le\frac FH\le b^n\Bigl(1+\frac1{2u-1}\Bigr)^n .
--   $$
--   Then $0\le\frac FH-b^n<1$.
--
--   With $F,H$ the Pell values for $bu$ and $u$, the integer part of $F/H$ is exactly $b^n$, provided $u$ is large.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Pell.lean#L173-L200

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

open OAI OAI.SingleFold

theorem OAI.SingleFold.PellAnalytics.quotient_error {b n c u : ℕ} (hu : (c+1)*(n+1)+4≤u)
    (hc : b^n≤c) {F H : ℝ} (_hH : 0<H)
    (hlo : (b:ℝ)^n≤F/H)
    (hhi : F/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n) :
    0≤F/H-(b:ℝ)^n ∧ F/H-(b:ℝ)^n<1 := by sorry
