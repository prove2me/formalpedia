-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_hasFDerivWithinAt
-- name    : OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:37:28.456116+00:00
-- url     : https://prove2.me/theorems/1d845c83-d76c-4ed1-80d3-4a0d8c59c6a5
-- title:
--   Gradient of the matrix energy at positive definite matrices
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. Let $P$ be positive definite. Then the energy $E(Q)=\operatorname{Re}\operatorname{tr}(Q\sqrt Q)$ is differentiable at $P$ within the positive semidefinite cone, with derivative
--   $$
--   DE(P)[K]=\frac32\operatorname{Re}\operatorname{tr}\bigl(\sqrt P\,K\bigr).
--   $$
--
--   This is the matrix version of $\frac{d}{dx}x^{3/2}=\frac32x^{1/2}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L682-L703

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

theorem OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    HasFDerivWithinAt energy (energyGradient P)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by sorry
