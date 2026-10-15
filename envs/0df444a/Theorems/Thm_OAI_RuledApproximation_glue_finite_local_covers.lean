-- Prove2me | Theorems.Thm_OAI_RuledApproximation_glue_finite_local_covers
-- name    : OAI.RuledApproximation.glue_finite_local_covers
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:49:44.875983+00:00
-- url     : https://prove2.me/theorems/aec21277-4690-483e-bfe7-4b88f5549a68
-- title:
--   Gluing local cylinder covers of a ruled set over finitely many patches with null frontier
-- statement:
--   For $h,L\in\mathbb{R}$, $Q\subseteq\mathbb{R}^2$ and $v:\mathbb{R}^2\to\mathbb{R}^2$ let $\mathcal R_h(Q,v,L)=\{(s,\ p_1+s\,v_1(p),\ h(p_2+s\,v_2(p))):\ p\in Q,\ |s|\le L\}\subseteq\mathbb{R}^3$. A *cylinder* in $\mathbb{R}^3$ has a unit axis $u$ and a base $B\subseteq u^\perp$; its carrier is $B+\mathbb{R}u$ and its area is the two-dimensional Lebesgue measure of $B$. Fix an arbitrary class $\mathcal S$ of cylinders (a "shape"), and say that $X\subseteq\mathbb{R}^3$ has an *$\mathcal S$-cover of cost at most* $C$ if finitely many cylinders of class $\mathcal S$ have carriers covering $X$ and areas summing to at most $C$.
--
--   Let $h,L,A\in\mathbb{R}$, $v:\mathbb{R}^2\to\mathbb{R}^2$ and $F:\mathbb{R}^2\to\mathbb{R}$. Let $I$ be a finite index set and, for $i\in I$, let $O_i,U_i\subseteq\mathbb{R}^2$ with $O_i$ open, $\overline{O_i}\subseteq U_i$ and $|\partial O_i|=0$ (Lebesgue measure). Assume the *local covering property*: for every $i\in I$, every compact $Q\subseteq U_i$ and every $\eta>0$, the set $\mathcal R_h(Q,v,L)$ has an $\mathcal S$-cover of cost at most $A\int_QF+\eta$. Then for every compact $K\subseteq\bigcup_{i\in I}O_i$ on which $F$ is integrable and every $\varepsilon>0$, the set $\mathcal R_h(K,v,L)$ has an $\mathcal S$-cover of cost at most
--   $$
--   A\int_KF(p)\,dp+\varepsilon.
--   $$
--
--   Only the frontiers of the patches $O_i$ need to be null; the compact set $K$ is arbitrary, and no sign condition on $A$ is required. Together with a compactness argument this turns local covers near each label into a global cover of the whole ruled set.
--
--   **Formalization Note** The index set is a `Finset` of an arbitrary type, and the shape is an arbitrary predicate `Cylinder → Prop`. A cylinder's area is `volume.real` of its base, which by Mathlib's convention is $0$ for a base of infinite measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean#L124-L162

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.glue_finite_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) {A : ℝ}
    {ι : Type*} (s : Finset ι) (O U : ι → Set Plane)
    (hO : ∀ i ∈ s, IsOpen (O i)) (hOU : ∀ i ∈ s, closure (O i) ⊆ U i)
    (hnull : ∀ i ∈ s, volume (frontier (O i)) = 0)
    (hlocal : ∀ i ∈ s, ∀ Q : Set Plane, IsCompact Q → Q ⊆ U i →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover shape (physicalRuled h Q v L)
        (A * (∫ p in Q, F p) + eps))
    {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hcover : K ⊆ ⋃ i ∈ s, O i) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ p in K, F p) + eps) := by sorry
