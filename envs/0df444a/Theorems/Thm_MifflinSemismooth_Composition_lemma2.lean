-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_lemma2
-- name    : MifflinSemismooth.Composition.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:43.001542+00:00
-- url     : https://prove2.me/theorems/ad88a06d-1b14-4a4d-af03-868ad656db30
-- title:
--   Lemma 2 — semismoothness yields directional derivatives and gradient-pairing limits
-- statement:
--   If $F$ is semismooth at $x$, then for every direction $d$ the one-sided directional derivative $F'(x;d)$ exists. For every sequence admitted by Definition 1, its generalized-gradient pairing converges to this derivative:
--
--   $$F'(x;d)=\lim_{k\to\infty}\langle g_k,d\rangle,\qquad g_k\in\partial F(x+t_kd+\theta_k),\quad t_k>0,\ t_k\to0,\ \theta_k/t_k\to0. $$
--
--   The two conclusions give a directional value shared by all admissible generalized-gradient sequences.
--
--   **Formalization Note** Existence of $F'(x;d)$ is expressed by the `HasDirDeriv` relation, with the same value used in the sequence limit.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 4, Lemma 2

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Composition

theorem lemma2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hFs : MifflinSemismooth.Extremal.SemismoothAt F x) :
    ∀ d, ∃ L, MifflinSemismooth.Extremal.HasDirDeriv F x d L ∧
      ∀ (t : ℕ → ℝ) (θ g : ℕ → EuclideanSpace ℝ (Fin n)),
        (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
        Tendsto (fun k => (t k)⁻¹ • θ k) atTop (𝓝 0) →
        (∀ k, g k ∈ MifflinSemismooth.Extremal.genGrad F (x + t k • d + θ k)) →
        Tendsto (fun k => inner ℝ (g k) d) atTop (𝓝 L) := by sorry

end MifflinSemismooth.Composition
