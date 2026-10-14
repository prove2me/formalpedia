-- Prove2me | Theorems.Thm_GaugeFunctor_not_faithful_of_toDiscrete
-- name    : GaugeFunctor.not_faithful_of_toDiscrete
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-14T00:40:48.573932+00:00
-- url     : https://prove2.me/theorems/27bd3c64-0efc-4854-aac9-af2d48636a61
-- title:
--   Functors from connections to a discrete category are never faithful
-- statement:
--   Let $X$ be a finite directed graph with at least one vertex, and let $G$ be a nontrivial group. Let $\mathcal A_G(X)$ be the groupoid whose objects are $G$-connections $A : E(X)\to G$ and whose arrows $A\to B$ are gauge transformations $g : V(X)\to G$ with $g\cdot A = B$, where $(g\cdot A)(e) = g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$.
--
--   **Statement.** For every set $\alpha$ and every functor $F : \mathcal A_G(X)\to \mathrm{Disc}(\alpha)$ into the discrete category on $\alpha$, $F$ is not faithful.
--
--   *Proof idea.* Take $a\in G$ with $a\neq 1$ and the trivial connection $A\equiv 1$. The constant gauge transformation $g\equiv a$ fixes $A$, since $a\cdot 1\cdot a^{-1}=1$, so it is an automorphism of $A$ different from the identity. A discrete category has only identity arrows, so $F(g)=F(\mathrm{id}_A)$.
--
--   This is the common "forgets structure" half of the Weatherall / Nguyen–Teh–Wells classification for every functor that records only gauge-invariant data, such as gauge orbits, field strengths and curvature conjugacy classes. Global (constant) gauge symmetries are always forgotten.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016), arXiv:1505.02229; J. Nguyen, N. Teh, L. Wells, Why Surplus Structure Is Not Superfluous, BJPS (2020), arXiv:1712.01228, §3.2

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- On a graph with at least one vertex and a nontrivial structure group `G`, no functor from
the groupoid of connections to a discrete category is faithful: the constant gauge
transformation `g ≡ a` with `a ≠ 1` is a nonidentity automorphism of the trivial connection,
but every functor into a discrete category sends it to the identity. -/
theorem not_faithful_of_toDiscrete (X : Graph) (G : Type) [Group G] [Nontrivial G]
    (hV : Nonempty (Fin X.nV)) {α : Type*} (F : PotG X G ⥤ Discrete α) : ¬ F.Faithful := by
  sorry

end GaugeFunctor
