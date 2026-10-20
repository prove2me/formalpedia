-- Prove2me | Theorems.Thm_OAI_SingleFold_PowerEstimate_growth_nat
-- name    : OAI.SingleFold.PowerEstimate.growth_nat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:19:47.955186+00:00
-- url     : https://prove2.me/theorems/7b6faab2-d7ca-4ad5-afc2-646154f7318d
-- title:
--   Growth bounds for the auxiliary function in natural form
-- statement:
--   Let $g:\mathbb{N}\to\mathbb{N}$, $\delta>0$ and $u\ge4$ with
--   $$
--   \delta(\log u)^2<\log g(u)<u\log u .
--   $$
--   Then $0<g(u)<u^u$.
--
--   So the growth function is positive and bounded by $u^u$. This bounds the size of the Pell witnesses by a value of $g$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L34-L48

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

theorem OAI.SingleFold.PowerEstimate.growth_nat {g : ℕ → ℕ} {δ : ℝ} {u : ℕ} (hδ : 0 < δ) (hu : 4≤u)
    (hg : δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    0<g u ∧ g u<u^u := by sorry
