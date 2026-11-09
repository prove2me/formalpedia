-- Prove2me | Theorems.Thm_Grunbaum2003_exists_small_apex_from_support_vertex_barycenter
-- name    : Grunbaum2003.exists_small_apex_from_support_vertex_barycenter
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:44:45.993528+00:00
-- url     : https://prove2.me/theorems/792c4d29-dea9-4165-b5df-276a5dc7da0a
-- title:
--   A small exterior apex from support-vertex barycentric data
-- statement:
--   Let $P\subseteq\mathbb R^d$ be convex, with $d>0$, and let $v_1,\ldots,v_d\in P$ lie on the supporting plane $\varphi(x)=a$, where $\varphi\le a$ on $P$. Suppose $\varphi(z)<a$. For finitely many additional linear constraints $\psi_j(x)\le c_j$, assume every selected vertex satisfies each constraint and at least one selected vertex satisfies it strictly for each $j$.
--
--   Writing
--
--   $$
--   w=\frac1d\sum_{i=1}^d v_i,
--   $$
--
--   we prove that $w\in P$, $\varphi(w)=a$, and there exists $0<t\le1$ such that
--
--   $$
--   y=w+t(w-z)\notin P,\qquad
--   \varphi(y)>a,\qquad
--   \psi_j(y)<c_j\quad\text{for every }j.
--   $$
--
--   Convexity puts the barycenter in $P$. Linearity makes its selected support value equal to $a$. For any additional constraint, averaging the vertex inequalities, including a strict inequality, gives $\psi_j(w)<c_j$.
--
--   Put $u=w-z$ and let $\delta_j=c_j-\psi_j(w)>0$. An explicit choice is
--
--   $$
--   B=\sum_j\frac{|\psi_j(u)|}{\delta_j},\qquad
--   t=\frac1{1+B}.
--   $$
--
--   Then $0<t\le1$, and each summand is at most $B$, so
--
--   $$
--   t|\psi_j(u)|<\delta_j.
--   $$
--
--   Thus every additional constraint remains strict at $w+tu$. Meanwhile $\varphi(u)=a-\varphi(z)>0$, so this point lies strictly beyond the selected support plane and hence outside $P$. The empty family of additional constraints is included: its sum is zero and $t=1$.
--
--   This is an elementary geometric step toward stellar subdivision. When the additional constraints are the other facet inequalities, it constructs an apex beneath them and beyond the selected facet. The theorem itself constrains those planes only on the selected vertices; identifying them as actual facet supports of $P$, obtaining the facet/vertex data, and proving the full simplicial face decomposition are further obligations. Affine independence of the selected vertices is not needed for this perturbation lemma.
-- source:
--   Elementary barycentric and finite-constraint perturbation argument, auxiliary to Grunbaum2003.exists_stellar_subdivision_cone_decomposition. The explicit parameter t=1/(1+sum |slope|/slack) and the complete proof are supplied here.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

theorem exists_small_apex_from_support_vertex_barycenter {d m : ℕ} (hd : 0 < d) {P : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (v : Fin d → Fin d → ℝ) (hvP : ∀ i, v i ∈ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hlevel : ∀ i, φ (v i) = a)
    (z : Fin d → ℝ) (hz : φ z < a)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother : ∀ j, (∀ i, ψ j (v i) ≤ c j) ∧ ∃ i, ψ j (v i) < c j) :
    let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
    w ∈ P ∧ φ w = a ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        a < φ (w + t • (w - z)) ∧
        w + t • (w - z) ∉ P ∧
        ∀ j, ψ j (w + t • (w - z)) < c j := by sorry

end Grunbaum2003
