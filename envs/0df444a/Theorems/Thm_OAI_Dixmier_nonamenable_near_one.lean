-- Prove2me | Theorems.Thm_OAI_Dixmier_nonamenable_near_one
-- name    : OAI.Dixmier.nonamenable_near_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:47:26.819674+00:00
-- url     : https://prove2.me/theorems/37a0ed50-2b98-4db8-823e-a0863d59ebcf
-- title:
--   Every non-amenable discrete group has a representation with $\|\pi(g)\|\le 1+\varepsilon$ that is not similar to a unitary one
-- statement:
--   Let $G$ be a group equipped with the discrete topology. Recall that $G$ is *amenable* if there is a $\mathbb{C}$-linear functional $m$ on the space $\ell^\infty(G)$ of bounded functions $G\to\mathbb{C}$ such that $m(\mathbf 1)=1$; $m(f)$ is a nonnegative real number whenever every value of $f$ is a nonnegative real number; and $m(\lambda_gf)=m(f)$ for all $g\in G$ and $f\in\ell^\infty(G)$, where $(\lambda_gf)(x)=f(g^{-1}x)$. A group homomorphism $\pi$ from $G$ into the algebra $B(H)$ of bounded linear operators on a complex Hilbert space $H$ is *similar to a unitary representation* if there is a bounded linear bijection $S$ of $H$ with bounded inverse such that $\|S\pi(g)S^{-1}x\|=\|x\|$ for all $g\in G$ and $x\in H$.
--
--   **Theorem.** Suppose that $G$ is not amenable, and let $\varepsilon>0$ be a real number. Then there exist a complex Hilbert space $H$ and a group homomorphism $\pi:G\to B(H)$ such that
--
--   1. if $G$ is countable, then $H$ is separable;
--   2. for every $g\in G$,
--   $$\|\pi(g)\|\le 1+\varepsilon ;$$
--   3. $\pi$ is not similar to a unitary representation.
--
--   Thus every non-amenable discrete group has uniformly bounded representations that are not unitarizable, with uniform bound arbitrarily close to $1$. Combined with the fact that uniformly bounded representations of amenable discrete groups are similar to unitary ones, this characterizes the amenable discrete groups as exactly the unitarizable ones.
--
--   **Formalization Note** The Hilbert space is a type `H` in the same universe as `G`, with explicit `NormedAddCommGroup`, `InnerProductSpace ℂ` and `CompleteSpace` structures, and separability is `TopologicalSpace.SeparableSpace H`. The representation is a monoid homomorphism `G →* (H →L[ℂ] H)`, and similarity is witnessed by a continuous linear equivalence. Bounded functions on $G$ are bounded continuous functions `G →ᵇ ℂ` for the discrete topology, and the mean in the definition of amenability is only required to be linear.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/NearOne.lean#L13-L83

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

open OAI OAI.Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem OAI.Dixmier.nonamenable_near_one (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by sorry
