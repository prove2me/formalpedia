-- Prove2me | Theorems.Thm_OAI_SingleFold_PellPower_ratio_bounds
-- name    : OAI.SingleFold.PellPower.ratio_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:13:34.163534+00:00
-- url     : https://prove2.me/theorems/bf7704b5-60b0-4f4d-b6f6-d18f78a6abaa
-- title:
--   The ratio of Pell solutions for $bu$ and $u$ approximates $b^n$
-- statement:
--   For an integer $a>1$ let $y_n(a)$ be the $y$-values of the Pell equation $x^2-(a^2-1)y^2=1$, so $y_0=0$, $y_1=1$ and $y_{n+2}=2ay_{n+1}-y_n$. For integers $b,u>1$ and every $n$,
--   $$
--   b^n\le\frac{y_{n+1}(bu)}{y_{n+1}(u)}\le b^n\Bigl(1+\frac1{2u-1}\Bigr)^n .
--   $$
--
--   When $u$ is large compared with $n$, the quotient of the two Pell values is within a small relative error of $b^n$. This lets $b^n$ be read off by integer division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Pell.lean#L88-L120

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

open OAI OAI.SingleFold OAI.SingleFold.PellPower
variable {a : ℕ} (ha : 1 < a)

theorem OAI.SingleFold.PellPower.ratio_bounds {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)^n ≤ (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ∧
    (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ≤
      (b:ℝ)^n*(1+1/(2*u-1))^n := by sorry
