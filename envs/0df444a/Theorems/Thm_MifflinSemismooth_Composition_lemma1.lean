-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_lemma1
-- name    : MifflinSemismooth.Composition.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:28.412706+00:00
-- url     : https://prove2.me/theorems/f9b9f9c5-586f-43f6-8a29-dbfcf4206d2a
-- title:
--   Lemma 1 — cluster points of difference quotients come from generalized gradients
-- statement:
--   Let $F$ be Lipschitz on an open set $B$ containing $x$. For a direction $d$, positive numbers $t_k\to0$, and shifts $h_k\to0$, every accumulation point $F^*$ of the difference quotients has the form
--
--   $$F^*=\langle g,d\rangle\quad\text{for some }g\in\partial F(x),\qquad \frac{F(x+h_k+t_kd)-F(x+h_k)}{t_k}. $$
--
--   The lemma connects directional limiting values to the generalized gradient at the base point.
--
--   **Formalization Note** The accumulation point is a `MapClusterPt`; no existence of a full quotient limit is assumed. The paper uses $t_k\downarrow0$ for positive convergence to zero.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 4, Lemma 1

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Composition

theorem lemma1 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B)
    (K : NNReal) (hFB : LipschitzOnWith K F B)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ B)
    (d : EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (htpos : ∀ k, 0 < t k) (htlim : Tendsto t atTop (𝓝 0))
    (h : ℕ → EuclideanSpace ℝ (Fin n))
    (hhlim : Tendsto h atTop (𝓝 0)) (Fstar : ℝ)
    (hcluster : MapClusterPt Fstar atTop
      (fun k => (F (x + h k + t k • d) - F (x + h k)) / t k)) :
    ∃ g ∈ MifflinSemismooth.Extremal.genGrad F x, Fstar = inner ℝ g d := by sorry

end MifflinSemismooth.Composition
