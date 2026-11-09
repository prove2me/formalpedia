-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stellar_apex_for_exposed_face
-- name    : Grunbaum2003.exists_stellar_apex_for_exposed_face
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:05:32.329087+00:00
-- url     : https://prove2.me/theorems/61ce4083-9a60-4415-97dc-a968cc38bb5d
-- title:
--   Exterior apex over an exposed face with exact old-vertex intersections
-- statement:
--   Let $P\subseteq\mathbb R^d$ be convex and let $F\ne P$ be a nonempty exposed face. Suppose every point $v_i$ is an exposed vertex of $P$ lying in $F$. We prove the existence of a point $y\notin P$ such that, for every subset $s\subseteq\operatorname{Fin}(d)$,
--
--   $$
--   \operatorname{conv}\bigl(\{y\}\cup v(s)\bigr)
--   \cap\{x:\{x\}\text{ is exposed in }P\}=v(s).
--   $$
--
--   The argument uses an exposing functional for $F$. A point strictly beyond its supporting hyperplane cannot contribute positive weight to a convex combination lying in $P$. Thus the cone intersects $P$ only in its base, and extremality of the old vertices identifies the intersection with the exposed vertices.
--
--   Choose $w\in F$ and an exposing linear functional $\varphi$. Set $c=\varphi(w)$. The definition of an exposed face gives
--
--   $$
--   \varphi(x)\le c\quad(x\in P),\qquad
--   \varphi(v_i)=c.
--   $$
--
--   Since $F$ is proper, there exists $z\in P\setminus F$. Then $\varphi(z)<c$. Define
--
--   $$
--   y=2w-z.
--   $$
--
--   Consequently $\varphi(y)=2c-\varphi(z)>c$, so $y\notin P$.
--
--   For a nonempty selected vertex set $A=v(s)$, every point of its cone has the form
--
--   $$
--   x=a y+b q,\qquad a,b\ge0,\quad a+b=1,\quad
--   q\in\operatorname{conv}(A).
--   $$
--
--   The functional is constant with value $c$ on the base hull. If $x\in P$, applying the supporting inequality yields
--
--   $$
--   a\varphi(y)+bc\le c=ac+bc.
--   $$
--
--   Since $\varphi(y)>c$, this forces $a=0$, and therefore $x=q$. Conversely the base hull lies in both the cone and $P$ by convexity. Hence
--
--   $$
--   \operatorname{conv}(\{y\}\cup A)\cap P=\operatorname{conv}(A).
--   $$
--
--   An exposed vertex of $P$ in this base hull is also an extreme point of the base hull. Extreme points of a convex hull belong to its generating set, so it lies in $A$. Every element of $A$ is already an exposed vertex of $P$, giving the claimed equality. When $A$ is empty, the cone is the singleton $\{y\}$, disjoint from $P$.
--
--   This auxiliary lemma supplies the exterior-apex and old-vertex-intersection conditions used in a stellar subdivision construction. It asserts neither that this particular apex lies beneath every other facet nor that its cones are the faces of a new simplicial polytope. Those geometric conditions remain separate obligations.
-- source:
--   Auxiliary supporting-hyperplane lemma for Grunbaum2003.exists_stellar_subdivision_cone_decomposition. Derived directly from the definition of an exposed face by reflecting w∈F away from z∈P\F. This is a separately proved elementary convexity lemma, not a claim that the reflected apex realizes the stellar subdivision.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem exists_stellar_apex_for_exposed_face {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) (hproper : F ≠ P)
    (v : Fin d → Fin d → ℝ)
    (hv : ∀ i, IsExposed ℝ P {v i}) (hvF : ∀ i, v i ∈ F) :
    ∃ y : Fin d → ℝ, y ∉ P ∧
      ∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d)) := by sorry

end Grunbaum2003
