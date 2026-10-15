-- Prove2me | Theorems.Thm_OAI_Dixmier_DayDixmier_mean_norm_le
-- name    : OAI.Dixmier.DayDixmier.mean_norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:51:09.331494+00:00
-- url     : https://prove2.me/theorems/0960edb5-e3f0-4da1-b4ce-d7ef15d8c212
-- title:
--   A normalized positive linear functional on bounded functions satisfies $|m(f)|\le 2\|f\|$
-- statement:
--   Let $G$ be a set carrying the discrete topology (no group structure is needed), and let $\ell^\infty(G)$ be the space of bounded functions $f:G\to\mathbb{C}$ with the supremum norm $\|f\|=\sup_{x\in G}|f(x)|$; write $\mathbf 1$ for the constant function $1$. Let $m:\ell^\infty(G)\to\mathbb{C}$ be a $\mathbb{C}$-linear functional, not assumed continuous, such that
--
--   - $m(\mathbf 1)=1$, and
--   - $m$ is positive: whenever every value $f(x)$ is a nonnegative real number, $m(f)$ is a nonnegative real number.
--
--   Then for every $f\in\ell^\infty(G)$,
--
--   $$
--   |m(f)|\le 2\,\|f\|.
--   $$
--
--   In particular such a functional is automatically bounded, with norm at most $2$; no invariance is assumed. The estimate is used to show that the averaged sesquilinear form $(x,y)\mapsto m(c_{x,y})$, built from the matrix coefficients $c_{x,y}(g)=\langle\pi(g^{-1})x,\pi(g^{-1})y\rangle$ of a uniformly bounded representation $\pi$, is bounded, which is the first step in the proof that uniformly bounded representations of amenable groups are similar to unitary ones.
--
--   **Formalization Note** $\ell^\infty(G)$ is the space `G →ᵇ ℂ` of bounded continuous functions, and $m$ is a `ℂ`-linear map to `ℂ`. Positivity is expressed through real and imaginary parts: if $\operatorname{Re}f(x)\ge0$ and $\operatorname{Im}f(x)=0$ for all $x$, then $\operatorname{Re}m(f)\ge0$ and $\operatorname{Im}m(f)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/MeanBounds.lean#L60-L85

import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MeanBounds

open OAI OAI.Dixmier OAI.Dixmier.DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [TopologicalSpace G]
variable [DiscreteTopology G]

theorem OAI.Dixmier.DayDixmier.mean_norm_le (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (f : G →ᵇ ℂ) : ‖m f‖ ≤ 2 * ‖f‖ := by sorry
