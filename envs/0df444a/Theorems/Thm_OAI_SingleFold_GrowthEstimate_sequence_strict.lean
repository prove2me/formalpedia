-- Prove2me | Theorems.Thm_OAI_SingleFold_GrowthEstimate_sequence_strict
-- name    : OAI.SingleFold.GrowthEstimate.sequence_strict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:06:50.753373+00:00
-- url     : https://prove2.me/theorems/4077eaff-ac1a-48aa-916d-7cc7ebf9a9a1
-- title:
--   A sequence with log-quadratic growth is strictly increasing
-- statement:
--   Let $W:\mathbb{N}\to\mathbb{N}$ with $W(j)>0$, and $a,c\in\mathbb{R}$ with $|\log W(j)-aj^2|\le c$ for all $j\ge1$. Assume moreover $W(0)=1$, $c\ge0$ and $2c<a$. Then
--   $$
--   W(0)<W(1)<W(2)<\cdots .
--   $$
--
--   Heights $W(j)=H(jP)$ on an elliptic curve satisfy such an estimate with $a$ the canonical height. So they increase strictly along multiples.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean#L11-L26

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

theorem OAI.SingleFold.GrowthEstimate.sequence_strict (hW : ∀ j, 0<W j) (hzero : W 0=1) (hc : 0≤c) (ha : 2*c<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) : StrictMono W := by sorry
