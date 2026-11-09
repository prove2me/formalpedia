-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_lemma_7
-- name    : GaussProcSparsify.Optimal.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:20.842754+00:00
-- url     : https://prove2.me/theorems/5418bdf6-00f7-415b-9e62-43604fef3911
-- title:
--   Lemma 7 — Gaussian integration by parts, in one and n dimensions
-- statement:
--   For every everywhere differentiable $f:\mathbb R\to\mathbb R$ whose derivative is integrable under $N(0,1)$,
--   $$\mathbb E[g f(g)]=\mathbb E[f'(g)].$$
--   For every $n$ and every $C^1$ function $F:\mathbb R^n\to\mathbb R$ such that $F$ and each partial derivative $\partial_iF$ are integrable under $\gamma_n$, one also has, for each coordinate $j$,
--   $$\mathbb E[g_jF(g)]=\mathbb E[\partial_jF(g)].$$
--   These are the two clauses of the printed lemma. No boundedness of derivatives or extra integrability of the products on the left is assumed. The identity supplies the Gaussian integration-by-parts input used to bound the shift vector field.
--
--   Differences from the source:
--   - encoding: $\mathbb R^n$ with the Euclidean norm and standard Gaussian law → `EuclideanSpace ℝ (Fin n)` and `stdGaussian`, including $n=0$; reason: these give the same inner product, norm and Gaussian distribution
--   - encoding: coordinates numbered $1,\ldots,n$ and partial derivatives $\partial_jF$ → coordinates in `Fin n`, with $DF(x)$ applied to the $j$th Euclidean basis vector; reason: this is the same coordinate derivative with indices shifted by one
--   - encoding: the expectations $\mathbb E[g f(g)]$ and $\mathbb E[g_jF(g)]$ → Bochner integrals, with no integrability hypothesis on the left-hand integrands; reason: the printed hypotheses already imply that $g f(g)$ and $g_jF(g)$ are integrable, so neither left side is a default value
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Lemma 7, PDF p. 12 (printed p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal

/-- Lemma 7, both the scalar identity and its coordinate consequence, PDF p. 12. -/
theorem lemma_7 :
    (∀ f : ℝ → ℝ, Differentiable ℝ f → Integrable (deriv f) (gaussianReal 0 1) →
      (∫ g, g * f g ∂gaussianReal 0 1) = ∫ g, deriv f g ∂gaussianReal 0 1) ∧
    (∀ (n : ℕ) (F : Vec n → ℝ), ContDiff ℝ 1 F → Integrable F (gaussian n) →
      (∀ i : Fin n, Integrable
        (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) (gaussian n)) →
      ∀ j : Fin n,
        (∫ g, g j * F g ∂gaussian n) =
          ∫ g, fderiv ℝ F g (EuclideanSpace.single j 1) ∂gaussian n) := by sorry

end GaussProcSparsify.Optimal
