-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_fourierSpace_mul
-- name    : OAI.LeanBlast.GotsmanLinial.fourierSpace_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:01.344191+00:00
-- url     : https://prove2.me/theorems/d6cd5cef-f154-4306-ab1a-30a24142ea2b
-- title:
--   Products of functions of Fourier degree at most $r$ and $s$ have Fourier degree at most $r+s$
-- statement:
--   Let $\chi_S(x)=\prod_{i\in S}x_i$ be the complex-valued Walsh characters on $\{-1,1\}^n$ and, for $k\in\mathbb{N}$, let $\mathcal V_k=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le k\}$. For all $r,s\in\mathbb{N}$ and all functions $a,b:\{-1,1\}^n\to\mathbb{C}$,
--
--   $$
--   a\in\mathcal V_r,\ \ b\in\mathcal V_s\ \Longrightarrow\ ab\in\mathcal V_{r+s},
--   $$
--
--   where $ab$ denotes the pointwise product.
--
--   Thus the Fourier degree filtration of the Boolean cube is multiplicative, the cube analogue of $\deg(fg)\le\deg f+\deg g$ for polynomials. It is used to place products of low-degree functions, for instance a conjugated test function times another low-degree function, in an explicit low-degree space.
--
--   **Formalization Note** $\mathcal V_k$ is `fourierSpace n k`. No cap at $n$ is imposed on $r+s$; for $k\ge n$ the space $\mathcal V_k$ is the whole function space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean#L122-L147

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff
variable {n d : ℕ}

theorem OAI.LeanBlast.GotsmanLinial.fourierSpace_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    a * b ∈ fourierSpace n (r + s) := by sorry
