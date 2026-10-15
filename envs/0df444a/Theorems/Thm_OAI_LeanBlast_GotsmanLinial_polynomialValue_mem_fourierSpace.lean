-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_polynomialValue_mem_fourierSpace
-- name    : OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:48:26.928652+00:00
-- url     : https://prove2.me/theorems/309cf84d-b6b2-4904-ab10-222e322c1834
-- title:
--   A multilinear polynomial of degree at most $d$ restricts to a cube function of Fourier degree at most $d$
-- statement:
--   For $S\subseteq\{1,\dots,n\}$ let $\chi_S:\{-1,1\}^n\to\mathbb{C}$, $\chi_S(x)=\prod_{i\in S}x_i$, be the Walsh character, and let $\mathcal V_d=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le d\}$ be the space of complex functions on the cube of Fourier degree at most $d$. Let $p\in\mathbb{R}[x_1,\dots,x_n]$ be multilinear (every monomial in its support has exponent at most $1$ in each variable) with total degree $\deg p\le d$. Then the function obtained by evaluating $p$ at the points of the cube and regarding the values as complex numbers lies in $\mathcal V_d$:
--
--   $$
--   \bigl(x\mapsto p(x)\bigr)\in\mathcal V_d=\operatorname{span}_{\mathbb{C}}\{\chi_S:\ |S|\le d\}.
--   $$
--
--   This is the bridge from the polynomial description of polynomial threshold functions to the Walsh–Fourier degree filtration of the Boolean cube, on which the spectral part of the Gotsman–Linial argument operates.
--
--   **Formalization Note** The cube is `Cube n` (Boolean vectors, `true` read as $1$ and `false` as $-1$), $p(x)$ is `polynomialValue p x`, i.e. `MvPolynomial.eval` at these $\pm1$ coordinates, coerced to $\mathbb{C}$. Multilinearity is `IsMultilinear p`, $\mathcal V_d$ is `fourierSpace n d`, and $d$ is an arbitrary natural number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean#L89-L103

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

theorem OAI.LeanBlast.GotsmanLinial.polynomialValue_mem_fourierSpace {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => (polynomialValue p x : ℂ)) ∈ fourierSpace n d := by sorry
