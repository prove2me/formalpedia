-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_projection_commutator
-- name    : OAI.LeanBlast.GotsmanLinial.projection_commutator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:41:59.379164+00:00
-- url     : https://prove2.me/theorems/d5ddaa38-4603-4340-9329-2c5da2a96b9d
-- title:
--   Commutator with a spectral grading multiplies each projection block by a weight difference
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets and let $(P_k)_{k\in\kappa}$ be an orthogonal decomposition of the identity in $\mathbb{C}^{\iota\times\iota}$: each $P_k$ is a Hermitian idempotent matrix, $P_rP_s=0$ for $r\ne s$, and $\sum_{k\in\kappa}P_k=I$. For real weights $\lambda:\kappa\to\mathbb{R}$ consider the grading (spectral multiplier)
--   $$G_\lambda=\sum_{k\in\kappa}\lambda_k\,P_k .$$
--   Then for every matrix $B\in\mathbb{C}^{\iota\times\iota}$ and all $r,s\in\kappa$,
--
--   $$
--   P_s\,\bigl(G_\lambda B-BG_\lambda\bigr)\,P_r=(\lambda_s-\lambda_r)\,P_s\,B\,P_r .
--   $$
--
--   Thus, in the block decomposition $B=\sum_{r,s}P_sBP_r$ determined by the projections, taking the commutator with $G_\lambda$ multiplies the $(s,r)$ block by the weight difference $\lambda_s-\lambda_r$. This is the basic identity behind Hilbert–Schmidt and entrywise estimates for commutators with a grading operator, such as the degree grading $\sum_k k\,P_k$.
--
--   **Formalization Note** The family is an `OrthogonalProjectionFamily P` (self-adjoint, idempotent, pairwise orthogonal, summing to $1$), and $G_\lambda$ is `matrixGrading P weight`. The real number $\lambda_s-\lambda_r$ is coerced to $\mathbb{C}$ and acts by scalar multiplication.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/ProjectionBlocks.lean#L78-L92

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators ComplexConjugate
open Module
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {P : κ → Matrix ι ι ℂ}

theorem OAI.LeanBlast.GotsmanLinial.projection_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B - B * matrixGrading P weight) * P r =
      ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by sorry
