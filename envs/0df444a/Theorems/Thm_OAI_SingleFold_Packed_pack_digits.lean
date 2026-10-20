-- Prove2me | Theorems.Thm_OAI_SingleFold_Packed_pack_digits
-- name    : OAI.SingleFold.Packed.pack_digits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:27:46.130043+00:00
-- url     : https://prove2.me/theorems/b99257c5-8bf0-4dec-99fe-ede44d4c5062
-- title:
--   A number is the packing of its own digits
-- statement:
--   For $B,k\in\mathbb{N}$ write $\mathrm{digit}_B(x,t)=\lfloor x/B^t\rfloor\bmod B$, $\mathrm{pack}_B(k,f)=\sum_{t<k}f(t)B^t$ and $\mathrm{ones}_B(k)=\mathrm{pack}_B(k,1)$. If $B>0$ and $x<B^k$, then
--   $$
--   \mathrm{pack}_B\bigl(k,\ t\mapsto\mathrm{digit}_B(x,t)\bigr)=x .
--   $$
--
--   Every number below $B^k$ is recovered from its first $k$ base-$B$ digits. This is the base-$B$ expansion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Packed.lean#L83-L96

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
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed

theorem OAI.SingleFold.Packed.pack_digits {B k x : ℕ} (hB : 0 < B) (hx : x < B^k) : pack B k (digit B x)=x := by sorry
