-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_lemma_10
-- name    : GaussProcSparsify.Optimal.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:48.54987+00:00
-- url     : https://prove2.me/theorems/4cd924f6-0f9c-4627-ae00-3709b4af93be
-- title:
--   Lemma 10 — Brascamp–Lieb variance inequality and its linear consequence
-- statement:
--   Let $V:\mathbb R^n\to\mathbb R$ be $C^2$ and satisfy $D^2V(x)[u,u]\ge\|u\|_2^2$ for every $x,u$. Let $\mu_V$ be the normalized law with density proportional to $e^{-V}$. Then every differentiable $f:\mathbb R^n\to\mathbb R$ satisfies
--   $$\operatorname{Var}_{\mu_V}(f)\le\int\|Df(x)\|_{\mathrm{op}}^2\,d\mu_V(x).$$
--   Variance and energy are extended nonnegative quantities, so infinite energy is allowed. On Euclidean space $\|Df(x)\|_{\mathrm{op}}=\|\nabla f(x)\|_2$. In particular, for every $u\in\mathbb R^n$,
--   $$\operatorname{Var}_{\mu_V}(\langle x,u\rangle)\le\|u\|_2^2.$$
--   Both clauses are retained. Neither square-integrability of $f$ nor an integrability hypothesis on $e^{-V}$ is added; the latter follows from the Hessian bound. This is the variance estimate for strongly log-concave laws required by the interpolation argument.
--
--   Differences from the source:
--   - encoding: a probability measure with density proportional to $e^{-V}$ → the computed measure `volume.tilted (fun x => -V x)`; reason: strong convexity gives a positive finite actual normalizer, and hence this is exactly the printed probability measure
--   - encoding: variance and expected squared gradient for any differentiable function → `evariance` and a nonnegative extended integral of the squared operator norm of $Df$; reason: these retain infinite energy rather than using a real integral default; finite energy forces integrability, and in Euclidean space the two gradient norms coincide
--   - encoding: $\mathbb R^n$ with the Euclidean norm and Lebesgue measure → `EuclideanSpace ℝ (Fin n)` with `volume`, including $n=0$; reason: these give the same inner product, norm and Lebesgue measure
--   - encoding: $V\in C^2$ and $\nabla^2V(x)\succeq I$ for every $x$ → `ContDiff ℝ 2 V` and `‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v` for all $x,v$; reason: the second Fréchet derivative applied to $(v,v)$ is the Hessian quadratic form
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 10, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gibbs

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal

/-- Lemma 10, PDF p. 13, with extended variance and extended energy.
The operator norm of Df equals the Euclidean norm of its gradient. -/
theorem lemma_10 {n : ℕ} (V : Vec n → ℝ) (hV : ContDiff ℝ 2 V)
    (hHess : ∀ x v : Vec n, ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) :
    (∀ f : Vec n → ℝ, Differentiable ℝ f →
      evariance f (gibbsLaw V) ≤ ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂gibbsLaw V) ∧
    (∀ u : Vec n,
      evariance (fun x => inner ℝ x u) (gibbsLaw V) ≤ ENNReal.ofReal (‖u‖ ^ 2)) := by sorry

end GaussProcSparsify.Optimal
