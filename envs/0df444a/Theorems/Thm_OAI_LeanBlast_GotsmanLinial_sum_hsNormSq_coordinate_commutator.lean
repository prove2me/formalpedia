-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_hsNormSq_coordinate_commutator
-- name    : OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:47:08.994988+00:00
-- url     : https://prove2.me/theorems/cd0b12f5-2bc8-4236-b85c-becd99442f80
-- title:
--   Coordinate commutator energy equals four times the Hamming-weighted entry energy
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the vertex set of the Boolean cube and write $x_i\in\{-1,1\}$ for the $i$-th coordinate of $x\in Q_n$. For each coordinate $i$ let $Z_i=\operatorname{diag}(x\mapsto x_i)$ be the $2^n\times2^n$ diagonal coordinate sign matrix, and let $d_H(x,y)=\#\{i:x_i\ne y_i\}$ be the Hamming distance. Then for every complex matrix $M=(M_{xy})_{x,y\in Q_n}$,
--
--   $$
--   \sum_{i=1}^{n}\bigl\|MZ_i-Z_iM\bigr\|_{\mathrm{HS}}^2\;=\;4\sum_{x,y\in Q_n}d_H(x,y)\,|M_{xy}|^2 ,
--   $$
--
--   where $\|A\|_{\mathrm{HS}}^2=\sum_{x,y}|A_{xy}|^2$ is the squared Hilbert–Schmidt norm.
--
--   The identity converts information about commutators with the coordinate multipliers into control of how much of the mass of $M$ sits far from the diagonal in Hamming distance. In the Gotsman–Linial argument the bounds $\|MZ_i-Z_iM\|_{\mathrm{HS}}^2\le2^n$ for the centred grading $M$ thereby become the distance-energy estimate $\sum_{x,y}d_H(x,y)|M_{xy}|^2\le n2^n/4$.
--
--   **Formalization Note** Vertices are Boolean vectors `Cube n` with `true` read as $1$ and `false` as $-1$; $Z_i$ is `coordinateSignMatrix i`, $d_H$ is Mathlib's `hammingDist`, and $\|\cdot\|_{\mathrm{HS}}^2$ is the explicit entry sum `hsNormSq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/CubeOperators.lean#L58-L78

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.GotsmanLinial.sum_hsNormSq_coordinate_commutator
    (M : Matrix (Cube n) (Cube n) ℂ) :
    (∑ i : Fin n, hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M)) =
      4 * ∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by sorry
