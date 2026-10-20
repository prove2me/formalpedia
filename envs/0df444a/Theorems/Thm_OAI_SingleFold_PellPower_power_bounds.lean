-- Prove2me | Theorems.Thm_OAI_SingleFold_PellPower_power_bounds
-- name    : OAI.SingleFold.PellPower.power_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:12:11.814968+00:00
-- url     : https://prove2.me/theorems/3846a86f-85c9-489c-a09f-f694b01916be
-- title:
--   Exponential bounds for Pell solutions
-- statement:
--   For an integer $a>1$ let $y_n(a)$ be the $y$-values of the Pell equation $x^2-(a^2-1)y^2=1$, so $y_0=0$, $y_1=1$ and $y_{n+2}=2ay_{n+1}-y_n$. Then for every $n$,
--   $$
--   (2a-1)^n\le y_{n+1}(a)\le(2a)^n .
--   $$
--
--   The Pell $y$-values grow essentially like $(2a)^n$. This is the source of exponential growth in Diophantine definitions of powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Pell.lean#L20-L34

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

theorem OAI.SingleFold.PellPower.power_bounds (n : ℕ) :
    (2*a-1)^n ≤ Pell.yn ha (n+1) ∧ Pell.yn ha (n+1) ≤ (2*a)^n := by sorry
