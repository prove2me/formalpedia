-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_lemma_23
-- name    : GaussProcSparsify.Optimal.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:23.115848+00:00
-- url     : https://prove2.me/theorems/9b04e276-b5c9-420e-8174-68b598af3dde
-- title:
--   Lemma 23 — Bounded continuous vector fields have global solutions
-- statement:
--   Let $F:[0,1]\times\mathbb R^N\to\mathbb R^N$ be continuous and bounded. Every initial value $a_0$ admits an absolutely continuous solution of
--   $$a'(\theta)=F(\theta,a(\theta))\text{ a.e.},\qquad a(0)=a_0.$$
--   Moreover, for every real bound $M$ with $\|F(\theta,x)\|_2\le M$ throughout the domain, every such solution obeys
--   $$\|a(\theta)-a(\theta')\|_2\le M|\theta-\theta'|\quad(\theta,\theta'\in[0,1]),\qquad\|a'(\theta)\|_2\le M\text{ a.e.}$$
--   Existence, the estimate for all solutions, and the almost-everywhere derivative bound are all part of the claim. No uniqueness or Lipschitz hypothesis on $F$ is imposed. This is the global existence statement needed for the shift system.
--
--   Differences from the source:
--   - encoding: paths defined on $[0,1]$, with derivatives for almost every parameter → functions on $\mathbb R$ constrained on $[0,1]$, and Lebesgue measure restricted to that interval; reason: every interval path admits an extension, and endpoints are null, so ambient derivatives and derivatives within the interval agree almost everywhere
--   - encoding: $\mathbb R^N$ with the Euclidean norm → `EuclideanSpace ℝ (Fin N)`, including $N=0$; reason: this is the same norm
--   - encoding: $F:[0,1]\times\mathbb R^N\to\mathbb R^N$ continuous and bounded → `F : ℝ × Vec N → Vec N`, continuous on and bounded on $[0,1]\times\mathbb R^N$; reason: values of $F$ at parameters outside $[0,1]$ are never used
--   - encoding: a solution of the initial-value problem → `IsODESolution`: Mathlib interval absolute continuity, the initial value, and the derivative within $[0,1]$ equal to $F$ for a.e. $\theta$; reason: this is the solution convention of PDF p. 15
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 23, PDF p. 38 (printed p. 37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Curves

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- Lemma 23, PDF p. 38: global existence and bounds for every solution. -/
theorem lemma_23 {N : ℕ} (F : ℝ × Vec N → Vec N)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x : Vec N, ‖F (θ, x)‖ ≤ M) :
    (∀ a₀ : Vec N, ∃ a : ℝ → Vec N, IsODESolution F a₀ a) ∧
    (∀ (M : ℝ), (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x : Vec N, ‖F (θ, x)‖ ≤ M) →
      ∀ (a₀ : Vec N) (a : ℝ → Vec N), IsODESolution F a₀ a →
        (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ θ' ∈ Set.Icc (0 : ℝ) 1,
          ‖a θ - a θ'‖ ≤ M * |θ - θ'|) ∧
        (∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖deriv a θ‖ ≤ M)) := by sorry

end GaussProcSparsify.Optimal
