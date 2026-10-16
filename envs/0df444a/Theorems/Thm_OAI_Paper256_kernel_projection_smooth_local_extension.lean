-- Prove2me | Theorems.Thm_OAI_Paper256_kernel_projection_smooth_local_extension
-- name    : OAI.Paper256.kernel_projection_smooth_local_extension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:38:25.845778+00:00
-- url     : https://prove2.me/theorems/656ab022-395d-4ded-8607-e50b93ce3b66
-- title:
--   Smooth local extension of the kernel projections of $E(I-uu^{\mathsf T})$ on the unit sphere
-- statement:
--   Let $c\ge1$, let $\mathrm{Sym}_k$ denote the real symmetric $k\times k$ matrices, and let $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$ be a real-linear map. For $M\in\mathbb{R}^{c\times c}$ let $K(M)\in\mathbb{R}^{c\times c}$ be the matrix of the orthogonal projection of $\mathbb{R}^c$ (standard inner product) onto $\ker M$. Vectors $u\in\mathbb{R}^4$ have coordinates $u_0,u_1,u_2,u_3$ and Euclidean norm $\|u\|$.
--
--   **Theorem.** There exist a unit vector $v\in\mathbb{R}^4$ with $v_0\neq0$, an open set $U\subseteq\mathbb{R}^4$ containing $v$, and a map $F:\mathbb{R}^4\to\mathbb{R}^{c\times c}$ that is $C^\infty$ on $U$, such that
--   $$
--   F(u)=K\big(E(I_4-uu^{\mathsf T})\big)\qquad\text{for every } u\in U \text{ with } \|u\|=1 .
--   $$
--
--   For a unit vector $u$, the matrix $I_4-uu^{\mathsf T}$ is the orthogonal projection onto $u^{\perp}$. The theorem says that the kernel projections of the matrices $E(I_4-uu^{\mathsf T})$, as $u$ moves on the unit sphere, agree near a suitable point $v$ (with $v_0\ne0$) with a smooth function. This is the input for differentiating these kernel projections along curves on the sphere.
--
--   **Formalization Note** $\mathbb{R}^4$ is `Vec 4 = EuclideanSpace ℝ (Fin 4)`, $uu^{\mathsf T}$ is `outerSym u`, and $K$ is `kernelProjection`, defined through `Matrix.toEuclideanLin` and the orthogonal projection `starProjection`. Smoothness is `ContDiffOn ℝ ∞`. The hypothesis $c>0$ is part of the statement, although the proof does not use it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/KernelSmooth.lean#L42-L72

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth

open OAI OAI.Paper256
open scoped ContDiff Matrix.Norms.L2Operator
open Set Matrix ContinuousLinearMap

theorem OAI.Paper256.kernel_projection_smooth_local_extension (c : ℕ) (_hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (U : Set (Vec 4)) (F : Vec 4 → Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ IsOpen U ∧ v ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ u ∈ U, ‖u‖ = 1 →
        F u = kernelProjection (E (1 - outerSym u) : Mat c ℝ) := by sorry
