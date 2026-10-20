-- Prove2me | Theorems.Thm_OAI_SingleFold_PellSystem_quotient_sound
-- name    : OAI.SingleFold.PellSystem.quotient_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:18:28.770334+00:00
-- url     : https://prove2.me/theorems/eeeda939-112d-479e-93e1-922f8d786d34
-- title:
--   Integer division of Pell values computes $b^n$
-- statement:
--   For an integer $a>1$ let $y_n(a)$ be the $y$-values of the Pell equation $x^2-(a^2-1)y^2=1$, so $y_0=0$, $y_1=1$ and $y_{n+2}=2ay_{n+1}-y_n$. Let $b\ge2$ and $u,n,c,r\in\mathbb{N}$ with $(c+1)(n+1)+4\le u$, and suppose
--   $$
--   y_{n+1}(bu)=c\cdot y_{n+1}(u)+r,\qquad r<y_{n+1}(u) .
--   $$
--   Then $c=b^n$.
--
--   This is the soundness half of the exponentiation system. Two Pell equations and one division with remainder determine $b^n$, provided the auxiliary parameter $u$ is large.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Pell.lean#L243-L271

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

theorem OAI.SingleFold.PellSystem.quotient_sound {b u n c r : ℕ} (hb : 2≤b) (hu : (c+1)*(n+1)+4≤u)
    (hdiv : Pell.yn (show 1<b*u by nlinarith) (n+1)=c*Pell.yn (show 1<u by nlinarith) (n+1)+r)
    (hr : r<Pell.yn (show 1<u by nlinarith) (n+1)) : c=b^n := by sorry
