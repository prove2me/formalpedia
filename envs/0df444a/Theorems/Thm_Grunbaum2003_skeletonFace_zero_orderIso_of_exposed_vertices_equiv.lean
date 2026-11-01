-- Prove2me | Theorems.Thm_Grunbaum2003_skeletonFace_zero_orderIso_of_exposed_vertices_equiv
-- name    : Grunbaum2003.skeletonFace_zero_orderIso_of_exposed_vertices_equiv
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:31.27452+00:00
-- url     : https://prove2.me/theorems/a2dc1ccc-2b24-4482-9718-744b1d9ab6a7
-- title:
--   Order isomorphism of $0$-skeletons from a bijection of exposed vertices
-- statement:
--   This theorem shows that any bijection between the sets of exposed vertices of two subsets $P \subseteq \mathbb{R}^{d_1}$ and $Q \subseteq \mathbb{R}^{d_2}$ induces an order isomorphism between their $0$-skeletons.
--
--   Let $d_1, d_2 \in \mathbb{N}$, let $P \subseteq \mathbb{R}^{d_1}$ and $Q \subseteq \mathbb{R}^{d_2}$, and suppose there is a bijection
--
--   $$
--   e : \bigl\{x \in \mathbb{R}^{d_1} \;\big|\; \operatorname{IsExposed}_{\mathbb{R}}(P, \{x\})\bigr\} \xrightarrow{\;\sim\;} \bigl\{y \in \mathbb{R}^{d_2} \;\big|\; \operatorname{IsExposed}_{\mathbb{R}}(Q, \{y\})\bigr\}
--   $$
--
--   between their sets of exposed vertices. Then their $0$-skeleton face posets are order-isomorphic:
--
--   $$
--   \operatorname{skel}_0(P) \simeq_{\mathrm{ord}} \operatorname{skel}_0(Q).
--   $$
--
--   Every element of the $0$-skeleton $\operatorname{skel}_0(P)$ is either the empty face $\emptyset$ or a singleton $\{x\}$ for an exposed vertex $x$ of $P$, because any nonempty set of affine dimension $0$ is a singleton. Thus $\operatorname{skel}_0(P)$ is canonically isomorphic to the flat pointed poset $\operatorname{Option}(\operatorname{vert}(P))$ with bottom element $\emptyset$ and incomparable atoms $\{x\}$, so any bijection of exposed vertices induces an order isomorphism of $0$-skeletons. In particular, for Joswig–Ziegler neighborly cubical polytopes (`neighborly_cubical_realization`) in dimensions $d \in \{2, 3\}$, where $\lfloor d/2 \rfloor - 1 = 0$, $0$-skeleton equivalence with the $n$-cube $[0,1]^n$ reduces to having the same number of exposed vertices.
--
--   **Formalization Note** The proof constructs an explicit bijection `skeletonFaceZeroFromOption P : Option {x | IsExposed ℝ P {x}} → SkeletonFace P 0` satisfying $a \le b \iff a = \mathrm{none} \lor a = b$ and transports it along `Equiv.optionCongr e`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.1 & §4.9, pp. 26–30, 69b

import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Order.Hom.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem skeletonFace_zero_orderIso_of_exposed_vertices_equiv (d₁ d₂ : ℕ)
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (e : {x : Fin d₁ → ℝ | IsExposed ℝ P {x}} ≃ {y : Fin d₂ → ℝ | IsExposed ℝ Q {y}}) :
    Nonempty (SkeletonFace P 0 ≃o SkeletonFace Q 0) := by sorry

end Grunbaum2003
