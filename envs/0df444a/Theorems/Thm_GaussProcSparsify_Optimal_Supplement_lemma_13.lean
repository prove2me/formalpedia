-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_lemma_13
-- name    : GaussProcSparsify.Optimal.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:22:06.851088+00:00
-- url     : https://prove2.me/theorems/fd632eb1-92e8-4407-b27b-233ad429c257
-- title:
--   Lemma 13 — strongly log-concave linear moments
-- statement:
--   There is a universal constant $C>0$ such that, for every dimension $n$ and every twice continuously differentiable $V:\mathbb R^n\to\mathbb R$ with $\nabla^2V(x)\succeq I$ everywhere, the normalized Gibbs law $d\mu\propto e^{-V}dx$ has integrable linear marginals and, for every $u\in\mathbb R^n$ and every finite real $p\ge2$,
--   $$\|\langle x,u\rangle-\mathbb E_\mu\langle x,u\rangle\|_{L^p(\mu)}\le C\sqrt p\,\|u\|_2.$$
--   The law is constructed from $V$ with its actual normalization. This moment estimate supports the Lᵖ extension and its geometric applications.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: Lᵖ error with finite real p≥2 → eLpNorm at ENNReal.ofReal p, compared to ENNReal.ofReal of the stated bound; reason: all source exponents are retained, and a divergent norm cannot satisfy a finite bound
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: the probability density proportional to exp(−V) and its linear expectation → the published normalized gibbsLaw V, with linear integrability concluded; reason: the C² Hessian bound guarantees normalization and integrability, so neither is assumed as an additional restriction
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 13, PDF p. 21 (printed p. 20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gibbs

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Lemma 13, PDF p. 21. A universal constant for every dimension, potential,
linear marginal, and finite real exponent p ≥ 2. Integrability is concluded. -/
theorem lemma_13 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (V : Vec n → ℝ), ContDiff ℝ 2 V →
      (∀ x v : Vec n, ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v) →
      ∀ (u : Vec n) (p : ℝ), 2 ≤ p →
        Integrable (fun x => inner ℝ x u) (gibbsLaw V) ∧
          eLpNorm (fun x => inner ℝ x u - ∫ y, inner ℝ y u ∂gibbsLaw V)
            (ENNReal.ofReal p) (gibbsLaw V) ≤ ENNReal.ofReal (C * Real.sqrt p * ‖u‖) := by sorry

end GaussProcSparsify.Optimal.Supplement
