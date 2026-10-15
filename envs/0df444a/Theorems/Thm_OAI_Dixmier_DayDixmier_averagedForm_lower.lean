-- Prove2me | Theorems.Thm_OAI_Dixmier_DayDixmier_averagedForm_lower
-- name    : OAI.Dixmier.DayDixmier.averagedForm_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:56:17.221986+00:00
-- url     : https://prove2.me/theorems/41102a02-6d6f-4db6-b62c-55ecf2c309da
-- title:
--   Lower bound $\|x\|^2\le M^2\,\mathrm{Re}\,m(c_{x,x})$ for averaged matrix coefficients of an $M$-bounded representation
-- statement:
--   Let $G$ be a group with the discrete topology, let $H$ be a complex inner product space (completeness is not needed), and let $\pi:G\to B(H)$ be a group homomorphism into the bounded linear operators on $H$. Let $M\ge0$ be a real number with $\|\pi(g)\|\le M$ for all $g\in G$. For $x\in H$ consider the matrix coefficient
--   $$c_{x,x}(g)=\bigl\langle\pi(g^{-1})x,\pi(g^{-1})x\bigr\rangle=\|\pi(g^{-1})x\|^2\qquad(g\in G),$$
--   a bounded function on $G$. Let $m$ be a $\mathbb{C}$-linear functional on the space $\ell^\infty(G)$ of bounded functions $G\to\mathbb{C}$ such that $m(\mathbf 1)=1$ and $m(f)$ is a nonnegative real number whenever every value of $f$ is a nonnegative real number. Then for every $x\in H$,
--
--   $$
--   \|x\|^2\le M^2\,\operatorname{Re} m\bigl(c_{x,x}\bigr).
--   $$
--
--   Neither invariance of $m$ nor completeness of $H$ is used. When $m$ is an invariant mean, the inequality says that the averaged inner product $\langle x,y\rangle_m=m(c_{x,y})$ dominates the original one up to the factor $M^2$; this coercivity makes the operator representing $\langle\cdot,\cdot\rangle_m$ invertible in the proof that uniformly bounded representations of amenable groups are similar to unitary ones.
--
--   **Formalization Note** The coefficient is `DayDixmier.coefficient π hM hπ x x`, a bounded continuous function `G →ᵇ ℂ` whose construction uses the hypotheses `hM : 0 ≤ M` and `hπ : ∀ g, ‖π g‖ ≤ M`. Positivity of $m$ is expressed through real and imaginary parts, and $m$ is not assumed continuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/AveragedForm.lean#L97-L125

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
import Definitions.Def_OAI_Analysis_Unitarizability_AveragedForm

open OAI OAI.Dixmier OAI.Dixmier.DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (π : G →* (H →L[ℂ] H)) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ g, ‖π g‖ ≤ M)

theorem OAI.Dixmier.DayDixmier.averagedForm_lower (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    ‖x‖^2 ≤ M^2 * (m (coefficient π hM hπ x x)).re := by sorry
