-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_hsNormSq_degreeGrading_commutator_le
-- name    : OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:46:42.537974+00:00
-- url     : https://prove2.me/theorems/fe47fd2f-8655-43ae-aaf0-23d91d7ef4f8
-- title:
--   Commuting a block-tridiagonal matrix with the degree grading does not increase its Hilbert–Schmidt norm
-- statement:
--   For a complex matrix $A$ indexed by a finite set write $\|A\|_{\mathrm{HS}}^2=\sum_{j,l}|A_{jl}|^2$ for its squared Hilbert–Schmidt (Frobenius) norm. Let $\iota$ be a finite index set, $n\in\mathbb{N}$, and let $P_0,\dots,P_n\in\mathbb{C}^{\iota\times\iota}$ be an orthogonal decomposition of the identity by Hermitian projections ($P_k^*=P_k=P_k^2$, $P_rP_s=0$ for $r\ne s$, $\sum_kP_k=I$), with degree grading $D=\sum_{k=0}^{n}k\,P_k$. If $Z\in\mathbb{C}^{\iota\times\iota}$ is block tridiagonal, i.e. $P_sZP_r=0$ whenever $|r-s|\ge2$, then
--
--   $$
--   \bigl\|DZ-ZD\bigr\|_{\mathrm{HS}}^2\;\le\;\|Z\|_{\mathrm{HS}}^2 .
--   $$
--
--   The commutator multiplies the $(s,r)$ block of $Z$ by $s-r$, and tridiagonality leaves only blocks with $|s-r|\le1$, so commuting with the grading cannot increase the Hilbert–Schmidt energy. For a unitary $Z$, such as a coordinate sign matrix of the Boolean cube, the right-hand side is the dimension of the space; in the Gotsman–Linial argument this bounds each coordinate commutator of the centred grading by $2^n$.
--
--   **Formalization Note** $\|A\|_{\mathrm{HS}}^2$ is the explicit entry sum `hsNormSq A`, not a matrix norm instance. Block tridiagonality (`BlockTridiagonal P Z`) is stated as $P_sZP_r=0$ whenever $r+1<s$ or $s+1<r$, and the family is an `OrthogonalProjectionFamily` indexed by `Fin (n + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean#L205-L225

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

theorem OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ hsNormSq Z := by sorry
