-- Prove2me | Theorems.Thm_OAI_Paper256_matrix_cfc_tendsto
-- name    : OAI.Paper256.matrix_cfc_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:48:08.020222+00:00
-- url     : https://prove2.me/theorems/3ad47c67-2958-4813-a63a-1d014ed8fee0
-- title:
--   Spectral functions of a symmetric matrix converge when they converge at its eigenvalues
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix with eigenvalues $\lambda_1,\dots,\lambda_n$ (listed with multiplicity), and for $h:\mathbb{R}\to\mathbb{R}$ let $h(A)=U\operatorname{diag}\bigl(h(\lambda_1),\dots,h(\lambda_n)\bigr)U^{\top}$ be the matrix obtained from the functional calculus, where $A=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)U^{\top}$ with $U$ orthogonal. Let $\mathcal{L}$ be a filter on an index set $T$ (for example $t\to\infty$ in $\mathbb{R}$, or $t\to t_0$), let $(f_t)_{t\in T}$ be a family of functions $\mathbb{R}\to\mathbb{R}$ and let $g:\mathbb{R}\to\mathbb{R}$. If
--   $$
--   \lim_{t\to\mathcal{L}} f_t(\lambda_i)=g(\lambda_i)\qquad\text{for every } i=1,\dots,n,
--   $$
--   then
--   $$
--   \lim_{t\to\mathcal{L}} f_t(A)=g(A)\qquad\text{in } \mathbb{R}^{n\times n}.
--   $$
--
--   No continuity of the $f_t$ or of $g$ is required: only convergence at the finitely many eigenvalues of $A$ matters. This allows limits whose target function is discontinuous at an eigenvalue, such as the indicator of $\{0\}$ at a zero eigenvalue, and it is used to compute limits of inverse square roots of matrices $I+(t-1)H$.
--
--   **Formalization Note** The filter is an arbitrary `L : Filter T`, convergence is `Tendsto`, the eigenvalues are `hA.eigenvalues` for the hypothesis `hA : A.IsHermitian`, and $h(A)$ is `cfc h A`. The space of matrices carries its standard (finite-dimensional) topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SpectralContinuity.lean#L14-L33

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
open Matrix Filter Topology
universe u

theorem OAI.Paper256.matrix_cfc_tendsto {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) {T : Type u} {L : Filter T}
    (f : T → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i, Tendsto (fun t => f t (hA.eigenvalues i)) L
      (𝓝 (g (hA.eigenvalues i)))) :
    Tendsto (fun t => cfc (f t) A) L (𝓝 (cfc g A)) := by sorry
