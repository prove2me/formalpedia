-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_lemma_24
-- name    : GaussProcSparsify.Optimal.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:06.873468+00:00
-- url     : https://prove2.me/theorems/087f1cf9-8161-4b70-a03e-7b9b6c9580f0
-- title:
--   Lemma 24 — Softmax paths are absolutely continuous in L²
-- statement:
--   Let $\iota$ be a nonempty finite index set, with absolutely continuous paths $v_t:[0,1]\to\mathbb R^n$ and $a_t:[0,1]\to\mathbb R$. Suppose $\|v'_t(\theta)\|_2\le L$ and $|a'_t(\theta)|\le M$ for each $t$ and almost every $\theta$, where $L,M$ are finite real constants. Fix $\beta>0$, and use the shared softmax $H_\theta$ and weights $\omega_t^\theta$.
--
--   There exists a curve in the actual normed space $L^2(\gamma_n)$ representing $H_\theta$ at every $\theta\in[0,1]$. It is absolutely continuous, and for almost every $\theta$ its derivative is represented by
--   $$\frac{d}{d\theta}H_\theta(g)=\sum_{t\in\iota}\omega_t^\theta(g)\bigl(\langle g,v'_t(\theta)\rangle+a'_t(\theta)\bigr).$$
--   The existence of the $L^2$ classes is concluded, not assumed. Absolute continuity and the identification of the derivative justify using the fundamental theorem of calculus for the softmax interpolation.
--
--   Differences from the source:
--   - encoding: $T$ finite in a logarithm of a sum of exponentials → a nonempty finite index type; reason: an empty sum gives an undefined logarithm in the source; arbitrary finite index types allow exactly the same family of paths
--   - encoding: paths defined on $[0,1]$, with derivatives for almost every parameter → functions on $\mathbb R$ constrained on $[0,1]$, and Lebesgue measure restricted to that interval; reason: every interval path admits an extension, and endpoints are null, so ambient derivatives and derivatives within the interval agree almost everywhere
--   - encoding: $\mathbb R^n$ with the Euclidean norm and standard Gaussian law → `EuclideanSpace ℝ (Fin n)` and `stdGaussian`, including $n=0$; reason: these give the same inner product, norm and Gaussian distribution
--   - encoding: $H_\theta$ and its derivative as elements of $L^2$ → existential curves and derivatives in `Lp ℝ 2 (gaussian n)`, with equality of representatives almost everywhere; reason: this constructs the actual equivalence classes without choosing representatives or assuming square-integrability as an extra hypothesis
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 24, PDF p. 39 (printed p. 38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Softmax
import Definitions.Def_GaussProcSparsify_Optimal_Curves

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- Lemma 24, PDF p. 39. H is constructed in L², not assumed to exist. -/
theorem lemma_24 {n : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ → Vec n) (a : ι → ℝ → ℝ)
    (hv : ∀ t, AbsolutelyContinuousOnInterval (v t) 0 1)
    (ha : ∀ t, AbsolutelyContinuousOnInterval (a t) 0 1)
    (L M : ℝ)
    (hL : ∀ t, ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖deriv (v t) θ‖ ≤ L)
    (hM : ∀ t, ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), |deriv (a t) θ| ≤ M)
    (β : ℝ) (hβ : 0 < β) :
    ∃ H : ℝ → Lp ℝ 2 (gaussian n),
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, IsL2Representative (softmax β v a θ) (H θ)) ∧
      AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∃ D : Lp ℝ 2 (gaussian n), IsL2Representative (softmaxVelocity β v a θ) D ∧
          HasDerivWithinAt H D (Set.Icc (0 : ℝ) 1) θ) := by sorry

end GaussProcSparsify.Optimal
