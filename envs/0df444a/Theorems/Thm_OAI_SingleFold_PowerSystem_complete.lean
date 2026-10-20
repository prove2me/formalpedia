-- Prove2me | Theorems.Thm_OAI_SingleFold_PowerSystem_complete
-- name    : OAI.SingleFold.PowerSystem.complete
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:22:16.465991+00:00
-- url     : https://prove2.me/theorems/0a5f8ad1-bdf7-4875-88ae-6ebc927f431b
-- title:
--   The power system has a solution with $c=b^n$
-- statement:
--   Let $g:\mathbb{N}\to\mathbb{N}$, $\delta>0$, $\ell\ge1$, $u_0\ge4$, with $\delta(\log u)^2<\log g(u)<u\log u$ for all $u\ge u_0$. The power system for $(b,n,c)$ asks for $w\in\mathbb{N}^9$ with $b\ge2$, $w_0=u:=(c+1)^\ell(n+1)(b+1)+u_0$, $w_1=g(w_0)$,
--   $$
--   w_2^2+w_3^2=1+(bw_0)^2w_3^2,\qquad w_4^2+w_5^2=1+w_0^2w_5^2,
--   $$
--   $0<w_3<w_1$, $0<w_5<w_1$, $w_3=n+1+(bw_0-1)w_6$, $w_5=n+1+(w_0-1)w_7$, $w_3=cw_5+w_8$ and $w_8<w_5$. Assume moreover $3<\delta\ell\log2$. Then for all $b\ge2$ and $n$ there is $w\in\mathbb{N}^9$ solving the power system for
--   $$
--   (b,\ n,\ c=b^n) .
--   $$
--
--   Together with soundness ($c=b^n$ is forced) and uniqueness of the witnesses, this gives a single-fold representation of exponentiation $(b,n)\mapsto b^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L174-L223

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

open OAI OAI.SingleFold OAI.SingleFold.PowerSystem
open PowerEstimate
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg

theorem OAI.SingleFold.PowerSystem.complete (hell' : 3<δ*(ell:ℝ)*Real.log 2) {b n : ℕ} (hb : 2≤b) :
    ∃ w, System g ell u₀ b n (b^n) w := by sorry
