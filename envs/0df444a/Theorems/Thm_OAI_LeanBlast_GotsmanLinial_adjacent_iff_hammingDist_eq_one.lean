-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_adjacent_iff_hammingDist_eq_one
-- name    : OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:11.187185+00:00
-- url     : https://prove2.me/theorems/b9676bb5-6a16-44cb-9523-b207f51e9a7b
-- title:
--   Two hypercube vertices differ by a single coordinate flip if and only if their Hamming distance is one
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the vertex set of the $n$-dimensional Boolean cube and, for a coordinate $i$ and $x\in Q_n$, let $x^{(i)}$ be the vertex obtained from $x$ by flipping its $i$-th coordinate. Call $x,y\in Q_n$ adjacent if $y=x^{(i)}$ for some coordinate $i$. Then for all $x,y\in Q_n$,
--
--   $$
--   \bigl(\exists\,i:\ y=x^{(i)}\bigr)\iff d_H(x,y)=1,
--   $$
--
--   where $d_H(x,y)=\#\{i:x_i\ne y_i\}$ is the Hamming distance.
--
--   This identifies the flip-based edge relation of the hypercube graph with its metric description. It allows ordered edges to be counted either as pairs (vertex, direction) or as ordered pairs of vertices at distance one, and is used to show that exactly $n2^n$ ordered pairs of vertices are at Hamming distance one.
--
--   **Formalization Note** Vertices are Boolean vectors `Cube n`, flipping is `flip i x` (Boolean negation of coordinate $i$), adjacency is `CubeAdjacent x y`, and $d_H$ is Mathlib's `hammingDist`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/SignParity.lean#L118-L141

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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem OAI.LeanBlast.GotsmanLinial.adjacent_iff_hammingDist_eq_one {n : ℕ} (x y : Cube n) :
    CubeAdjacent x y ↔ hammingDist x y = 1 := by sorry
