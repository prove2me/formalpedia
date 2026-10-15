-- Prove2me | Theorems.Thm_OAI_Dixmier_DayDixmier_representation_similar
-- name    : OAI.Dixmier.DayDixmier.representation_similar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:01:02.584339+00:00
-- url     : https://prove2.me/theorems/5da91962-1829-44c9-909c-498550a01a86
-- title:
--   Uniformly bounded representations of amenable discrete groups on Hilbert spaces are similar to unitary representations
-- statement:
--   Let $G$ be a group with the discrete topology, and suppose $G$ is amenable: there is a $\mathbb{C}$-linear functional $m$ on the space $\ell^\infty(G)$ of bounded functions $G\to\mathbb{C}$ with $m(\mathbf 1)=1$, such that $m(f)$ is a nonnegative real number whenever every value of $f$ is a nonnegative real number, and such that $m(\lambda_gf)=m(f)$ for all $g\in G$, $f\in\ell^\infty(G)$, where $(\lambda_gf)(x)=f(g^{-1}x)$. Let $H$ be a complex Hilbert space and let $\pi:G\to B(H)$ be a group homomorphism into the bounded linear operators on $H$ that is uniformly bounded: there is a real constant $C$ with $\|\pi(g)\|\le C$ for all $g\in G$.
--
--   Then $\pi$ is similar to a unitary representation: there is a bounded linear bijection $S:H\to H$ with bounded inverse such that
--
--   $$
--   \bigl\|S\,\pi(g)\,S^{-1}x\bigr\|=\|x\|\qquad\text{for all }g\in G\text{ and }x\in H .
--   $$
--
--   This is the classical Day–Dixmier unitarization theorem for discrete groups, and it is the direction "amenable implies unitarizable" of the characterization of amenable discrete groups by their uniformly bounded representations. No countability of $G$ or separability of $H$ is required, and the bound $C$ may be arbitrary.
--
--   **Formalization Note** $H$ is a type with `NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` structures, in an arbitrary universe. The representation is a monoid homomorphism `G →* (H →L[ℂ] H)`, so each $\pi(g)$ is invertible with inverse $\pi(g^{-1})$, and $S$ is a continuous linear equivalence `H ≃L[ℂ] H`. Bounded functions are bounded continuous functions `G →ᵇ ℂ` for the discrete topology, and the mean is only required to be linear.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Amenable.lean#L12-L65

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

theorem OAI.Dixmier.DayDixmier.representation_similar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hG : Amenable G) (π : G →* (H →L[ℂ] H))
    (hb : ∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) : SimilarToUnitary π := by sorry
