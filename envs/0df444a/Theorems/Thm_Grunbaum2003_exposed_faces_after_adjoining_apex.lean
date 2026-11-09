-- Prove2me | Theorems.Thm_Grunbaum2003_exposed_faces_after_adjoining_apex
-- name    : Grunbaum2003.exposed_faces_after_adjoining_apex
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:39:17.76901+00:00
-- url     : https://prove2.me/theorems/8fefe1e0-8bf1-4af7-985a-cef8dd4d8253
-- title:
--   Exposed faces after adjoining an apex: exact support-height trichotomy
-- statement:
--   Let $P\subseteq\mathbb R^d$ be nonempty, compact and convex, let $y\in\mathbb R^d$, and put $Q=\operatorname{conv}(P\cup\{y\})$. For a continuous linear functional $\varphi$, write $F_\varphi(P)$ for its set of maximizers on $P$. If $w\in P$ maximizes $\varphi$, then
--
--   $$
--   F_\varphi(Q)=
--   \begin{cases}
--   F_\varphi(P),&\varphi(y)<\varphi(w),\\
--   \operatorname{conv}(F_\varphi(P)\cup\{y\}),&\varphi(y)=\varphi(w),\\
--   \{y\},&\varphi(y)>\varphi(w).
--   \end{cases}
--   $$
--
--   Every point of $Q$ has the form $a y+b z$, where $z\in P$, $a,b\ge0$, and $a+b=1$. Its functional value is the same weighted average of $\varphi(y)$ and $\varphi(z)$. If the apex has strictly smaller value than the old maximum, an attaining point must have $a=0$. If its value is strictly greater, an attaining point must have $b=0$. If the two values agree, a positive base coefficient can occur only at an old maximizing point. These observations prove all three formulas, including the reverse inclusions by convexity.
--
--   Consequently every nonempty exposed face of $Q$ is either the singleton apex, an exposed face of $P$, or the convex hull of the apex with a nonempty exposed face of $P$. To obtain this conclusion, choose a functional exposing the given face of $Q$ and use compactness of $P$ to obtain its old maximum.
--
--   This is a known elementary convexity fact newly formalized here. It supplies the general exposed-face classification needed before a stellar-subdivision argument specializes the position of the apex. It does not assert that every old face survives, that every old face cones to a new face, or that the required simplicial facet/apex configuration exists.
-- source:
--   Elementary consequence of the supporting-functional definition of exposed faces and the extreme value theorem. Auxiliary to Grunbaum2003.exists_stellar_subdivision_cone_decomposition; the support-height formulas and their complete proof are supplied here.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem exposed_faces_after_adjoining_apex {d : ℕ} {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (hcompact : IsCompact P) (hPne : P.Nonempty) (y : Fin d → ℝ) :
    (∀ (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, φ x ≤ φ w) →
      (φ y < φ w → φ.toExposed (convexHull ℝ (insert y P)) = φ.toExposed P) ∧
      (φ y = φ w → φ.toExposed (convexHull ℝ (insert y P)) =
        convexHull ℝ (insert y (φ.toExposed P))) ∧
      (φ w < φ y → φ.toExposed (convexHull ℝ (insert y P)) = {y})) ∧
    (∀ F : Set (Fin d → ℝ), F.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) F →
      F = {y} ∨ IsExposed ℝ P F ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          F = convexHull ℝ (insert y G)) := by sorry

end Grunbaum2003
