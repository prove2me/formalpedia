-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_fourierSpace_star
-- name    : OAI.LeanBlast.GotsmanLinial.fourierSpace_star
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:48:56.459319+00:00
-- url     : https://prove2.me/theorems/e963ffaa-8f25-4279-a9d6-e6d96dd966a5
-- title:
--   The Walsh degree filtration is closed under complex conjugation
-- statement:
--   Let $\chi_S(x)=\prod_{i\in S}x_i$ (for $S\subseteq\{1,\dots,n\}$ and $x\in\{-1,1\}^n$) be the Walsh characters of the Boolean cube, regarded as complex-valued functions, and let $\mathcal V_d=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le d\}$ be the space of functions of Fourier degree at most $d$. If $a:\{-1,1\}^n\to\mathbb{C}$ lies in $\mathcal V_d$, then so does its pointwise complex conjugate:
--
--   $$
--   a\in\mathcal V_d\ \Longrightarrow\ \bar a\in\mathcal V_d,\qquad\text{where }\bar a(x)=\overline{a(x)} .
--   $$
--
--   Combined with multiplicativity of the filtration, this controls the Fourier degree of products such as $\bar b\,a$ that arise in Hermitian pairings of low-degree functions.
--
--   **Formalization Note** $\mathcal V_d$ is `fourierSpace n d`, a complex submodule of the functions on `Cube n`, and $\bar a$ is `star a`, i.e. pointwise complex conjugation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean#L105-L120

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

theorem OAI.LeanBlast.GotsmanLinial.fourierSpace_star {a : Cube n → ℂ} (ha : a ∈ fourierSpace n d) :
    star a ∈ fourierSpace n d := by sorry
