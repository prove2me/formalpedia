-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_norm_energyGradient_inserted_gram_le
-- name    : OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:47:00.37613+00:00
-- url     : https://prove2.me/theorems/c11b7b38-1eef-485f-9b11-5edf7d35d9e8
-- title:
--   Operator-norm bound for the energy gradient on inserted Gram matrices
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. For square matrices $R,L$,
--   $$
--   \bigl|\nabla E(R^*R)[R^*LR]\bigr|\le\frac32\,\|\operatorname{tr}_{\mathbb R}\|\,\|L\|\,\|R\|^3 ,
--   $$
--   where $\nabla E(P)[K]=\frac32\operatorname{Re}\operatorname{tr}(\sqrt PK)$, the norms of matrices are $\ell^2$ operator norms, and $\|\operatorname{tr}_{\mathbb R}\|$ is the norm of the real trace functional.
--
--   The gradient is cubic in $R$, as expected for the energy $\operatorname{tr}(R^*R)^{3/2}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/NormBounds.lean#L42-L62

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le (R L : Matrix ι ι ℂ) :
    ‖energyGradient (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/2 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖ * ‖R‖^3 := by sorry
