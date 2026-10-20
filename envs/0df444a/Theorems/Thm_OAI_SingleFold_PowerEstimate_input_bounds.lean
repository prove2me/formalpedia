-- Prove2me | Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds
-- name    : OAI.SingleFold.PowerEstimate.input_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:19:09.707334+00:00
-- url     : https://prove2.me/theorems/78d38577-a4b9-4edb-a07d-9155f0805f37
-- title:
--   Size bounds for the input of the exponentiation system
-- statement:
--   For $\ell,u_0,b,n,c\in\mathbb{N}$ let $u=(c+1)^\ell(n+1)(b+1)+u_0$. If $\ell\ge1$ and $u_0\ge4$, then
--   $$
--   u_0\le u,\qquad(c+1)(n+1)+4\le u,\qquad b<u,\qquad n+1<u-1 .
--   $$
--
--   These bounds make $u$ a valid auxiliary parameter for the Pell quotient: it dominates all quantities that appear.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L17-L32

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

theorem OAI.SingleFold.PowerEstimate.input_bounds {ell u₀ b n c : ℕ} (hell : 1≤ell) (h₀ : 4≤u₀) :
    u₀ ≤ input ell u₀ b n c ∧ (c+1)*(n+1)+4 ≤ input ell u₀ b n c ∧
    b < input ell u₀ b n c ∧ n+1 < input ell u₀ b n c-1 := by sorry
