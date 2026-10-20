-- Prove2me | Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_lower
-- name    : OAI.SingleFold.DuplicationBound.height_dup_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:02:49.866775+00:00
-- url     : https://prove2.me/theorems/959db176-3845-427b-8b9e-7e0414efd91a
-- title:
--   Doubling raises the height to roughly the fourth power
-- statement:
--   For a rational $x$ let $h(x)=\max(|\mathrm{num}(x)|,\mathrm{den}(x))$ in lowest terms, and let $\mathrm{dup}(x)=\dfrac{(x^2+25)^2}{4x(x^2-25)}$ be the $x$-coordinate of $2P$ on $y^2=x^3-25x$ when $x(P)=x$. If $x\ne0$ and $x^2\ne25$, then
--   $$
--   h(x)^4\le6250000\cdot h(\mathrm{dup}(x)) .
--   $$
--
--   Only a bounded common factor can cancel between the numerator and the denominator of the duplication formula. This is the elementary form of the quadratic growth of heights under doubling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Duplication.lean#L55-L97

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

open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound

theorem OAI.SingleFold.DuplicationBound.height_dup_lower (x : ℚ) (hx : x ≠ 0) (hs : x^2-25 ≠ 0) :
    height x ^ 4 ≤ 6250000 * height (dupX x) := by sorry
