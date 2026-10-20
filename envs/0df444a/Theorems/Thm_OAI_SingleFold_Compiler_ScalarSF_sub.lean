-- Prove2me | Theorems.Thm_OAI_SingleFold_Compiler_ScalarSF_sub
-- name    : OAI.SingleFold.Compiler.ScalarSF.sub
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:22:45.749679+00:00
-- url     : https://prove2.me/theorems/79737255-0e9b-4029-80e3-70b78c375bdb
-- title:
--   Truncated subtraction of single-fold functions is single-fold
-- statement:
--   A function $f:\mathbb{N}^\alpha\to\mathbb{N}$ is scalar-SF if its graph $\{(x,v):v=f(x)\}$ has a single-fold Diophantine representation. If $f$ and $g$ are scalar-SF, then so is
--   $$
--   x\mapsto f(x)\mathbin{\dot-}g(x)=\max\bigl(f(x)-g(x),0\bigr) .
--   $$
--
--   Truncated subtraction is needed, for instance, to compute remainders and differences of packed numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean#L230-L244

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

open OAI OAI.SingleFold OAI.SingleFold.Compiler
variable {α : Type} {f g : (α → ℕ) → ℕ}

theorem OAI.SingleFold.Compiler.ScalarSF.sub (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z-g z) := by sorry
