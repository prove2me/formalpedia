-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_steinitz
-- name    : IPProximity.Eisenbrand.steinitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:31:57.14399+00:00
-- url     : https://prove2.me/theorems/f828df2c-0a3b-4765-9c72-6f306e8db814
-- title:
--   Theorem 1.1 (Steinitz) with constant $c(m)=m$
-- statement:
--   Let $E$ be a real normed space of finite dimension $m$ (for example $\mathbb R^m$ with an arbitrary norm $\|\cdot\|$). Let $x_1,\dots,x_n\in E$ satisfy
--   $$\sum_{i=1}^n x_i=0\qquad\text{and}\qquad \|x_i\|\le1\ \text{ for each } i.$$
--   Then there is a permutation $\pi\in S_n$ such that all partial sums satisfy
--   $$\Big\|\sum_{j=1}^k x_{\pi(j)}\Big\|\le m\qquad\text{for all } k=1,\dots,n.$$
--
--   This is the Steinitz lemma with the constant $c(m)=m$ due to Sevast'anov, which the paper quotes right after Theorem 1.1 and uses (for the $\ell_\infty$ norm) in the proof of Theorem 3.3.
--
--   **Formalization Note** The norm is any norm on $E$ given by a `NormedAddCommGroup`/`NormedSpace ℝ` structure (hence symmetric), and $m$ is `Module.finrank ℝ E`. The partial sum of length $k$ is the sum over indices $j<k$ of `Fin n`.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:4, Theorem 1.1 and the following sentence (c(m) ⩽ m, Sevast'anov); p. 5:3 (arbitrary norm of R^m)

import Mathlib

namespace IPProximity.Eisenbrand

/-- Theorem 1.1 (Steinitz) with Sevast'anov's constant `c(m) = m` (p. 5:4): in an
`m`-dimensional real normed space, vectors of norm at most `1` summing to zero can be ordered so
that every partial sum `x_{π(1)} + ⋯ + x_{π(k)}`, `1 ≤ k ≤ n`, has norm at most `m`. -/
theorem steinitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m n : ℕ} (hdim : Module.finrank ℝ E = m) (x : Fin n → E)
    (hsum : ∑ i, x i = 0) (hnorm : ∀ i, ‖x i‖ ≤ 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ‖∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), x (σ j)‖ ≤ (m : ℝ) := by sorry

end IPProximity.Eisenbrand
