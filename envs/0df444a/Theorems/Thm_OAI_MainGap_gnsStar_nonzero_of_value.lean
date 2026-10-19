-- Prove2me | Theorems.Thm_OAI_MainGap_gnsStar_nonzero_of_value
-- name    : OAI.MainGap.gnsStar_nonzero_of_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:02:26.539269+00:00
-- url     : https://prove2.me/theorems/f4c29b11-b77b-4c6a-b6de-705bd1d3d7dd
-- title:
--   The GNS representation of $g$ does not vanish at $a$ when $g(a^*a)\neq0$
-- statement:
--   Let $B$ be a unital C$^*$-algebra, ordered by its positive cone, and let $g$ be a positive linear functional on $B$. A *positive linear functional* on a C$^*$-algebra $B$ is a $\mathbb{C}$-linear map $g:B\to\mathbb{C}$ that preserves order, where $\mathbb{C}$ carries the partial order $z\le w$ iff $\operatorname{Re}z\le\operatorname{Re}w$ and $\operatorname{Im}z=\operatorname{Im}w$. Equivalently, $g(x)$ is a nonnegative real number whenever $x\ge0$. The GNS construction equips $B$ with the semi-inner product $\langle x,y\rangle_g=g(x^*y)$. Its Hilbert-space completion $H_g$, in which vectors of seminorm zero are identified with $0$, carries the unital $*$-representation $\pi_g:B\to B(H_g)$ determined by $\pi_g(a)[x]=[ax]$, where $[x]\in H_g$ denotes the image of $x\in B$.
--
--   **Theorem.** For every $a\in B$,
--   $$g(a^*a)\neq0\ \Longrightarrow\ \pi_g(a)\neq0 .$$
--
--   The number $g(a^*a)$ is the squared length of the vector $\pi_g(a)[1]=[a]$, so a nonzero value of $g$ on $a^*a$ is witnessed by the GNS representation. The result certifies that representations obtained from the GNS construction, for instance from ultralimits of vector functionals, do not annihilate a given element.
--
--   **Formalization Note** $H_g$ and $\pi_g$ are Mathlib's `g.GNS` and `g.gnsStarAlgHom`. The order on $B$ is any partial order making $B$ a star-ordered ring, which is necessarily the positive-cone order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Representation.lean#L79-L95

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

theorem OAI.MainGap.gnsStar_nonzero_of_value {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (g : B →ₚ[ℂ] ℂ) (a : B)
    (ha : g (star a * a) ≠ 0) : g.gnsStarAlgHom a ≠ 0 := by sorry
