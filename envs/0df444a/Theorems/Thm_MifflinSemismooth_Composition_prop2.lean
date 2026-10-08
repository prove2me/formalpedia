-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_prop2
-- name    : MifflinSemismooth.Composition.prop2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:36.939643+00:00
-- url     : https://prove2.me/theorems/433c937f-261a-456d-834d-adf8be80377a
-- title:
--   Proposition 2 — Lebourg mean value theorem
-- statement:
--   Let $F$ be Lipschitz on an open set $B$, and let $y,z$ lie in a convex subset of $B$. There are $0<\lambda<1$ and $g\in\partial F(y+\lambda(z-y))$ such that
--
--   $$F(z)-F(y)=\langle g,z-y\rangle. $$
--
--   This nonsmooth mean value identity is used to relate difference quotients to generalized gradients.
--
--   **Formalization Note** The open-set Lipschitz constant is an `NNReal`; the convex subset is explicit. The generalized gradient is the paper's support-set definition.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 2

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

namespace MifflinSemismooth.Composition

theorem prop2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B)
    (K : NNReal) (hFB : LipschitzOnWith K F B)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C)
    (hCB : C ⊆ B) (y z : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ C) (hz : z ∈ C) :
    ∃ lam ∈ Set.Ioo (0 : ℝ) 1,
      ∃ g ∈ MifflinSemismooth.Extremal.genGrad F (y + lam • (z - y)),
        F z - F y = inner ℝ g (z - y) := by sorry

end MifflinSemismooth.Composition
