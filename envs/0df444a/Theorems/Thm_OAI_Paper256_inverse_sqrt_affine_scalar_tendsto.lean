-- Prove2me | Theorems.Thm_OAI_Paper256_inverse_sqrt_affine_scalar_tendsto
-- name    : OAI.Paper256.inverse_sqrt_affine_scalar_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:48:40.743793+00:00
-- url     : https://prove2.me/theorems/5247bdd0-76c7-4524-abc4-44f9ac38ac07
-- title:
--   Limit of $1/\sqrt{1+(t-1)\mu}$ as $t\to\infty$
-- statement:
--   Let $\mu$ be a real number with $\mu\ge 0$. Then, as the real variable $t$ tends to $+\infty$,
--   $$
--   \lim_{t\to+\infty}\frac{1}{\sqrt{1+(t-1)\mu}}=\begin{cases}1, & \mu=0,\\ 0, & \mu>0.\end{cases}
--   $$
--
--   The limit is the indicator function of $\{0\}$ evaluated at $\mu$. Applied to the eigenvalues $\mu$ of a positive semidefinite matrix $H$, it is the scalar input showing that the inverse square roots of $I+(t-1)H$ converge to the orthogonal projection onto $\ker H$.
--
--   **Formalization Note** The expression is defined for every real $t$ through Lean's conventions $\sqrt{x}=0$ for $x<0$ and $0^{-1}=0$; for $t\ge 1$ the radicand is at least $1$, so these conventions do not affect the limit, which is taken along the filter `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SpectralContinuity.lean#L35-L48

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

theorem OAI.Paper256.inverse_sqrt_affine_scalar_tendsto (μ : ℝ) (hμ : 0 ≤ μ) :
    Tendsto (fun t : ℝ => (Real.sqrt (1 + (t - 1) * μ))⁻¹) atTop
      (𝓝 (if μ = 0 then 1 else 0)) := by sorry
