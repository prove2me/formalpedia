-- Prove2me | Theorems.Thm_OAI_Paper256_kernelProjection_eq_cfc
-- name    : OAI.Paper256.kernelProjection_eq_cfc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:47:07.644194+00:00
-- url     : https://prove2.me/theorems/c808c60a-73da-4c66-ab6b-c293102ec131
-- title:
--   The kernel projection of a symmetric matrix is its spectral projection at the eigenvalue $0$
-- statement:
--   Let $n\ge 0$ and let $H$ be a real symmetric $n\times n$ matrix with spectral decomposition $H=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)U^{\top}$, $U$ orthogonal. For a function $f:\mathbb{R}\to\mathbb{R}$, the matrix $f(H)=U\operatorname{diag}\bigl(f(\lambda_1),\dots,f(\lambda_n)\bigr)U^{\top}$ is given by the functional calculus (it does not depend on the choice of $U$). Let $\Pi_{\ker H}$ be the matrix of the orthogonal projection of $\mathbb{R}^n$, with its Euclidean inner product, onto the kernel of $H$, and let $\mathbf{1}_{\{0\}}$ be the indicator function of $\{0\}$, i.e. $\mathbf{1}_{\{0\}}(x)=1$ if $x=0$ and $0$ otherwise. Then
--
--   $$
--   \Pi_{\ker H}=\mathbf{1}_{\{0\}}(H).
--   $$
--
--   Thus the orthogonal projection onto the kernel is the spectral projection of $H$ belonging to the eigenvalue $0$ (it is the zero matrix when $0$ is not an eigenvalue). This expresses kernel projections through the functional calculus, so that they can be obtained as limits of matrices $f_t(H)$ whenever $f_t\to\mathbf{1}_{\{0\}}$ at the eigenvalues of $H$; for instance, inverse square roots of $I+(t-1)H$ converge to $\Pi_{\ker H}$ when $H\succeq 0$ and $t\to\infty$.
--
--   **Formalization Note** `kernelProjection A` is defined as the matrix of `starProjection` onto the kernel of `A.toEuclideanLin`, and $f(H)$ is Mathlib's continuous functional calculus `cfc f H`, which for a symmetric matrix applies $f$ to the eigenvalues; every function is continuous on the finite spectrum, so no hypothesis on $f$ is needed. The case $n=0$ is included.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SpectralProjection.lean#L20-L81

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

theorem OAI.Paper256.kernelProjection_eq_cfc {n : ℕ} (H : Sym n) :
    kernelProjection (H : Mat n ℝ) =
      cfc (fun x : ℝ => if x = 0 then 1 else 0) (H : Mat n ℝ) := by sorry
