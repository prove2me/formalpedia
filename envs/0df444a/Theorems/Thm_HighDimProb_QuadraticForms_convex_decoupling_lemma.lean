-- Prove2me | Theorems.Thm_HighDimProb_QuadraticForms_convex_decoupling_lemma
-- name    : HighDimProb.QuadraticForms.convex_decoupling_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:58.637244+00:00
-- url     : https://prove2.me/theorems/b4350311-665a-4229-9d9c-6d29dc2a1500
-- title:
--   Lemma 6.1.2 — the convex decoupling lemma
-- statement:
--   This is the technical seed of the decoupling technique used throughout Chapter 6 of
--   Vershynin's *High-Dimensional Probability*: a two-line consequence of Jensen's
--   inequality.
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space and let $Y, Z : \Omega \to \mathbb R$
--   be independent random variables with $\mathbb E Z = 0$. Then, for every convex function
--   $F : \mathbb R \to \mathbb R$,
--
--   $$
--   \mathbb E\, F(Y) \;\le\; \mathbb E\, F(Y + Z).
--   $$
--
--   In words: adding an independent, mean-zero perturbation to a random variable can only
--   increase the expectation of any convex function of it. This is the single inequality
--   from which the Decoupling theorem (Theorem 6.1.1) is built, by conditioning on all
--   variables but a mean-zero remainder term at each step of its proof.
--
--   **Formalization Note** $Y$ and $Z$ are required measurable, and `Integrable Z P` is
--   added alongside $\mathbb E Z = 0$: Mathlib's Bochner integral defaults to $0$ for a
--   non-integrable function, so without integrability the hypothesis $\mathbb E Z = 0$ could
--   hold vacuously for a $Z$ that is not genuinely mean zero, and the conclusion could then
--   fail. `F` convex is Mathlib's `ConvexOn ℝ Set.univ F` (convex on the whole real line, as
--   the book states). Integrability of $F(Y)$ and $F(Y+Z)$ is likewise assumed so that both
--   sides of the conclusion are genuine expectations rather than Mathlib's junk value $0$.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Lemma 6.1.2, p. 136 (PDF p. 144)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

/-- **Lemma 6.1.2** (the convex decoupling lemma), Vershynin, *High-Dimensional Probability*
(2018), p. 136.

Let `Y` and `Z` be independent random variables such that `E Z = 0`. Then, for every convex
function `F`, one has `E F(Y) ≤ E F(Y + Z)`. -/
theorem convex_decoupling_lemma {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hindep : IndepFun Y Z P) (hZint : Integrable Z P) (hZmean : ∫ ω, Z ω ∂P = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hYF : Integrable (fun ω => F (Y ω)) P)
    (hYZF : Integrable (fun ω => F (Y ω + Z ω)) P) :
    ∫ ω, F (Y ω) ∂P ≤ ∫ ω, F (Y ω + Z ω) ∂P := by sorry

end HighDimProb.QuadraticForms
