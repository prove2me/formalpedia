-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_liouville
-- name    : HunterPDE.Harmonic.liouville
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:06:01.967005+00:00
-- url     : https://prove2.me/theorems/0d1743dd-e59c-4988-a5a4-4709149588a9
-- title:
--   Corollary 2.8 — Liouville: a bounded harmonic function on ℝⁿ is constant
-- statement:
--   If $u \in C^2(\mathbb{R}^n)$ is bounded and harmonic in $\mathbb{R}^n$, then $u$ is constant: there is $c \in \mathbb{R}$ with
--   $$u(x) = c \qquad \text{for all } x \in \mathbb{R}^n.$$
--
--   This is the $n$-dimensional analogue of Liouville's theorem for bounded entire functions.
--
--   **Formalization Note.** Harmonic in $\mathbb{R}^n$ is `InnerProductSpace.HarmonicOnNhd u Set.univ`; bounded is $\exists M, \forall x, |u(x)| \le M$. The statement holds for every $n$, including the trivial $n = 0$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 23, Corollary 2.8

import Mathlib

namespace HunterPDE.Harmonic

/-- Corollary 2.8 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 23 (Liouville): if
`u ∈ C²(ℝⁿ)` is bounded and harmonic in `ℝⁿ`, then `u` is constant. -/
theorem liouville {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u Set.univ) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) :
    ∃ c : ℝ, ∀ x, u x = c := by sorry

end HunterPDE.Harmonic
