-- Prove2me | Theorems.Thm_OAI_Paper256_exists_smooth_kernel_extension
-- name    : OAI.Paper256.exists_smooth_kernel_extension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:37:51.080107+00:00
-- url     : https://prove2.me/theorems/c12176e0-aa53-4f2e-9264-c5ec07257143
-- title:
--   Kernel projections of a smooth self-adjoint operator family extend smoothly near some point
-- statement:
--   Let $W$ be a real normed vector space and $\mathcal H$ a finite-dimensional real inner product space, and write $\mathcal L(\mathcal H)$ for the space of linear operators on $\mathcal H$. For an operator $T$ let $\Pi_{\ker T}$ denote the orthogonal projection of $\mathcal H$ onto $\ker T$. Let $S\subseteq W$ be a nonempty set and let $A:W\to\mathcal L(\mathcal H)$ be a $C^\infty$ map such that $A(u)$ is self-adjoint for every $u\in S$.
--
--   **Theorem.** There exist a point $v\in S$, an open set $U\subseteq W$ with $v\in U$, and a map $P:W\to\mathcal L(\mathcal H)$ that is $C^\infty$ on $U$, such that
--   $$
--   P(u)=\Pi_{\ker A(u)}\qquad\text{for all } u\in U\cap S .
--   $$
--
--   The kernel projection $u\mapsto\Pi_{\ker A(u)}$ of a smooth family is in general not even continuous, because the kernel can jump when the rank changes. The theorem says that, near a suitably chosen point of $S$, the kernel projections along $S$ are nevertheless restrictions of a smooth map. This makes it possible to differentiate kernel projections along curves that stay in $S$.
--
--   **Formalization Note** $\mathcal L(\mathcal H)$ is the space `F →L[ℝ] F` of continuous linear maps with its operator norm, smoothness is `ContDiff ℝ ∞` and `ContDiffOn ℝ ∞` (infinitely differentiable), and $\Pi_{\ker A(u)}$ is `(A u).ker.starProjection`. Self-adjointness is required only at points of $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/KernelLocal.lean#L14-L66

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

open OAI OAI.Paper256
open scoped ContDiff RealInnerProductSpace
open Set ContinuousLinearMap
universe u v

theorem OAI.Paper256.exists_smooth_kernel_extension
    {W : Type u} {F : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set W) (hne : S.Nonempty) (A : W → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hs : ∀ u ∈ S, IsSelfAdjoint (A u)) :
    ∃ v ∈ S, ∃ (U : Set W) (P : W → F →L[ℝ] F),
      IsOpen U ∧ v ∈ U ∧ ContDiffOn ℝ ∞ P U ∧
      ∀ u ∈ U, u ∈ S → P u = (A u).ker.starProjection := by sorry
