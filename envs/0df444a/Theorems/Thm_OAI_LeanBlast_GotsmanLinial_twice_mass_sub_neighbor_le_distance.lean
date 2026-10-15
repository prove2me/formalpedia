-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_twice_mass_sub_neighbor_le_distance
-- name    : OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:48.247213+00:00
-- url     : https://prove2.me/theorems/dc8054af-927a-4d4d-b24b-a8342b568b4e
-- title:
--   Shell inequality: distance-weighted mass controls total mass off the distance-one shell
-- statement:
--   Let $\alpha$ be a finite set, $d:\alpha\to\mathbb{N}$ a distance-like function, and $w:\alpha\to\mathbb{R}$ nonnegative weights, $w(a)\ge0$ for all $a\in\alpha$. For $k\in\mathbb{N}$ let $S_k=\{a\in\alpha:d(a)=k\}$ be the shell at distance $k$. Then
--
--   $$
--   2\sum_{a\in\alpha}w(a)-\sum_{a\in S_1}w(a)\;\le\;2\sum_{a\in S_0}w(a)+\sum_{a\in\alpha}d(a)\,w(a).
--   $$
--
--   Equivalently, the distance-weighted mass $\sum_a d(a)w(a)$, increased by twice the mass at distance $0$, is at least the total mass counted twice off the shell $S_1$ and once on it. In the edge-recovery step of the Gotsman–Linial argument it is applied with $\alpha$ the ordered pairs of cube vertices, $d$ the Hamming distance and $w$ the squared moduli of the entries of a matrix.
--
--   **Formalization Note** The shells $S_k$ are `distanceShell d k`, the finite set of $a$ with $d(a)=k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean#L33-L55

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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem OAI.LeanBlast.GotsmanLinial.twice_mass_sub_neighbor_le_distance (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    2 * (∑ a, w a) - (∑ a ∈ distanceShell d 1, w a) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) + ∑ a, (d a : ℝ) * w a := by sorry
