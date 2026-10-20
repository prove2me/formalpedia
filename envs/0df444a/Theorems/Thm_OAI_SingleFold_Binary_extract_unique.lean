-- Prove2me | Theorems.Thm_OAI_SingleFold_Binary_extract_unique
-- name    : OAI.SingleFold.Binary.extract_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:25:24.935232+00:00
-- url     : https://prove2.me/theorems/518d9c53-8874-4c2a-816b-edecfd73fd80
-- title:
--   Extracting a middle digit from a mixed-radix decomposition
-- statement:
--   Let $B,H,N,s,d,r\in\mathbb{N}$ with
--   $$
--   N=sBH+dH+r,\qquad d<B,\qquad r<H .
--   $$
--   Then $r=N\bmod H$, $d=\lfloor N/H\rfloor\bmod B$ and $s=\lfloor\lfloor N/H\rfloor/B\rfloor$.
--
--   The witnesses $s,d,r$ in the binary-domination system are therefore determined by $N,B,H$. This gives uniqueness of the witness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Binary.lean#L94-L106

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

open OAI OAI.SingleFold OAI.SingleFold.Binary

theorem OAI.SingleFold.Binary.extract_unique {B H N s d r : ℕ} (h : N=s*B*H+d*H+r) (hd : d<B) (hr : r<H) :
    r=N%H ∧ d=N/H%B ∧ s=N/H/B := by sorry
