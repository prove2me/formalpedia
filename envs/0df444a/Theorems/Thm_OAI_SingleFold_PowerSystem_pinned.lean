-- Prove2me | Theorems.Thm_OAI_SingleFold_PowerSystem_pinned
-- name    : OAI.SingleFold.PowerSystem.pinned
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:21:29.948632+00:00
-- url     : https://prove2.me/theorems/53baac5a-fa7f-4900-b53d-dfe36b99624c
-- title:
--   Solutions of the power system are the Pell solutions of index $n+1$
-- statement:
--   Let $g:\mathbb{N}\to\mathbb{N}$, $\delta>0$, $\ell\ge1$, $u_0\ge4$, with $\delta(\log u)^2<\log g(u)<u\log u$ for all $u\ge u_0$. The power system for $(b,n,c)$ asks for $w\in\mathbb{N}^9$ with $b\ge2$, $w_0=u:=(c+1)^\ell(n+1)(b+1)+u_0$, $w_1=g(w_0)$,
--   $$
--   w_2^2+w_3^2=1+(bw_0)^2w_3^2,\qquad w_4^2+w_5^2=1+w_0^2w_5^2,
--   $$
--   $0<w_3<w_1$, $0<w_5<w_1$, $w_3=n+1+(bw_0-1)w_6$, $w_5=n+1+(w_0-1)w_7$, $w_3=cw_5+w_8$ and $w_8<w_5$. For an integer $a>1$ let $(x_k(a),y_k(a))$ be the solutions of the Pell equation $x^2-(a^2-1)y^2=1$. Then every solution $w$ of the power system for $(b,n,c)$ satisfies
--   $$
--   (w_2,w_3)=\bigl(x_{n+1}(bw_0),y_{n+1}(bw_0)\bigr),\qquad(w_4,w_5)=\bigl(x_{n+1}(w_0),y_{n+1}(w_0)\bigr).
--   $$
--
--   The four Pell witnesses are therefore uniquely determined by the inputs. This makes the power system single-fold.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L126-L139

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

theorem OAI.SingleFold.PowerSystem.pinned {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) :
    w 2=px (b*w 0) (n+1) ∧ w 3=py (b*w 0) (n+1) ∧
    w 4=px (w 0) (n+1) ∧ w 5=py (w 0) (n+1) := by sorry
