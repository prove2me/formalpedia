-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_grading_commutator_phase_identity
-- name    : OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:45:54.377291+00:00
-- url     : https://prove2.me/theorems/bd38d8ca-fb91-4b47-8971-44b2b7f3d991
-- title:
--   Phase-conjugation formula for the commutator of the degree grading with a block-tridiagonal matrix
-- statement:
--   Let $\iota$ be a finite index set, $n\in\mathbb{N}$, and let $P_0,\dots,P_n\in\mathbb{C}^{\iota\times\iota}$ be an orthogonal decomposition of the identity: Hermitian idempotents with $P_rP_s=0$ for $r\ne s$ and $\sum_{k=0}^nP_k=I$. Define the degree grading and the phase matrix
--   $$D=\sum_{k=0}^{n}k\,P_k,\qquad U=\sum_{k=0}^{n}i^k\,P_k ,$$
--   where $i$ is the imaginary unit. Let $Z\in\mathbb{C}^{\iota\times\iota}$ be block tridiagonal for this decomposition, i.e. $P_sZP_r=0$ whenever $|r-s|\ge2$. Then
--
--   $$
--   2i\,\bigl(DZ-ZD\bigr)=UZU^{*}-U^{*}ZU ,
--   $$
--
--   where $U^*$ denotes the conjugate transpose of $U$.
--
--   The phase matrix $U$ is unitary, so for unitary $Z$ the identity writes the commutator $DZ-ZD$ as $(2i)^{-1}$ times a difference of two unitary matrices; in particular every entry of $DZ-ZD$ then has modulus at most $1$. In the Gotsman–Linial argument $Z$ is a coordinate sign matrix of the Boolean cube, which is block tridiagonal for the grading constructed there, and this entry bound yields the cap on the off-diagonal entries of the centred grading.
--
--   **Formalization Note** The decomposition is an `OrthogonalProjectionFamily` indexed by `Fin (n + 1)`; $D$ is `degreeGrading P`, $U$ is `gradingPhase P`, and $U^*$ is `star (gradingPhase P)`. Block tridiagonality (`BlockTridiagonal P Z`) is the condition $P_sZP_r=0$ whenever $r+1<s$ or $s+1<r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean#L170-L189

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators Matrix
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

theorem OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) (htri : BlockTridiagonal P Z) :
    (2 * Complex.I) • (degreeGrading P * Z - Z * degreeGrading P) =
      gradingPhase P * Z * star (gradingPhase P) -
        star (gradingPhase P) * Z * gradingPhase P := by sorry
