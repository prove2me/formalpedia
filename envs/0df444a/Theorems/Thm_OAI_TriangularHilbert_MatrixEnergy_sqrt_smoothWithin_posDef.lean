-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sqrt_smoothWithin_posDef
-- name    : OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:36:43.617061+00:00
-- url     : https://prove2.me/theorems/bb94f90c-b03c-491e-90c2-7114bc92d82c
-- title:
--   Smoothness of the matrix square root at positive definite matrices
-- statement:
--   Let $P$ be a positive definite complex matrix. Then the matrix square root $Q\mapsto\sqrt Q$ is $C^\infty$ at $P$ within the cone of positive semidefinite matrices. Its derivative there is the inverse of the Sylvester operator of $\sqrt P$:
--   $$
--   D\sqrt{\,\cdot\,}(P)[K]=Y\quad\text{where}\quad\sqrt P\,Y+Y\sqrt P=K .
--   $$
--
--   Here $\mathrm{sylv}_{\sqrt P}:X\mapsto\sqrt PX+X\sqrt P$ is invertible because $\sqrt P$ is positive definite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L627-L655

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι uκ uX uμ
open scoped BigOperators
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
variable {ι : Type uι} [Fintype ι]
variable [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ContDiffWithinAt ℝ ∞ CFC.sqrt {Q : Matrix ι ι ℂ | 0 ≤ Q} P ∧
    HasFDerivWithinAt CFC.sqrt
      ((sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm : _ →L[ℝ] _)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by sorry
