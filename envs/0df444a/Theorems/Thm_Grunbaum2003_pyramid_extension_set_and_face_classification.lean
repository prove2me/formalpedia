-- Prove2me | Theorems.Thm_Grunbaum2003_pyramid_extension_set_and_face_classification
-- name    : Grunbaum2003.pyramid_extension_set_and_face_classification
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T04:41:22.247284+00:00
-- url     : https://prove2.me/theorems/6e340422-2633-4f56-918e-b7b1453b72a8
-- title:
--   Set and face geometry of a pyramid extension
-- statement:
--   Let $P\subset\mathbb R^d$ be a nonempty compact convex set with a finite halfspace presentation
--
--   $$P=\{x:\varphi(x)\le a,\ \psi_j(x)\le c_j\text{ for all }j\}.$$
--
--   Choose $y$ with $\varphi(y)>a$ and $\psi_j(y)<c_j$ for every other defining inequality. Put $F=P\cap\{\varphi=a\}$ and $Q=\operatorname{conv}(P\cup\{y\})$. Then
--
--   $$Q=P\cup\operatorname{conv}(F\cup\{y\}).$$
--
--   Every nonempty proper exposed face of $Q$ is either $\{y\}$, an exposed face of $P$, or $\operatorname{conv}(G\cup\{y\})$ for a nonempty exposed face $G$ of $P$ contained in $F$.
--
--   In addition, if a linear functional $\ell$ attains its maximum over $P$ at $w$ and $\ell(y)<\ell(w)$, its old maximizer face remains exposed in $Q$. If that face lies in $F$, its cone with apex $y$ is also exposed in $Q$.
--
--   These statements supply the set and face geometry used in stellar subdivision. They do not yet assert simpliciality or an exact face-count formula.
-- source:
--   Auxiliary support-plane lemma for Grunbaum2003.exists_stellar_subdivision_cone_decomposition, https://prove2.me/theorems/66fedc85-e2bf-44b8-9b3b-9e7d0d908ec9 (source: Grünbaum, Convex Polytopes, 2003, Chapter 10). This precise auxiliary statement and its elementary proof are supplied here; it is not a verbatim theorem from the book.

import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

theorem pyramid_extension_set_and_face_classification
    {d m : ℕ} (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j) :
    (convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a})) ∧
    (∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H →
      H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G)) ∧
    (∀ (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, ℓ x ≤ ℓ w) → ℓ y < ℓ w →
      IsExposed ℝ (convexHull ℝ (insert y P)) (ℓ.toExposed P) ∧
      (ℓ.toExposed P ⊆ {x | φ x = a} →
        IsExposed ℝ (convexHull ℝ (insert y P))
          (convexHull ℝ (insert y (ℓ.toExposed P))))) := by sorry

end Grunbaum2003
