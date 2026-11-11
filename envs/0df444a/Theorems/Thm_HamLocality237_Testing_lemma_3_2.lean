-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_2
-- name    : HamLocality237.Testing.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:15.902278+00:00
-- url     : https://prove2.me/theorems/d019cde3-7178-4d0d-8378-c4751b30b45a
-- title:
--   Definition 3.1 and Lemma 3.2 — hard law and both moments
-- statement:
--   For $0<\varepsilon<1/2$, the specified bump has norm one, $M$ and $J_\varepsilon$ are self-adjoint, and $\|J_\varepsilon\|\le1$. The constructed spectral measure $\nu_\varepsilon$ is a probability measure supported on $[-1,1]$, uniquely characterized by
--
--   $$\int f(h)\,d\nu_\varepsilon(h)=\langle\perp,f(J_\varepsilon)\perp\rangle$$
--
--   for continuous complex $f$. Such test functions are integrable. Both moments exist and satisfy
--
--   $$\mathbb E[h]=0,\qquad\mathbb E[h^2]=\varepsilon^2.$$
--
--   This records the definition's well-definedness guarantees together with the complete two-clause moment lemma. The measure is constructed from the actual block operator, rather than supplied as a variable.
--
--   Differences from the source:
--   - encoding: a Borel probability measure and continuous tests on [-1,1] → a real-line Borel measure with zero mass outside [-1,1], tested by global continuous complex functions via real and imaginary functional calculus; reason: restriction and extension identify these measures; every continuous interval function extends to the real line, so the characterization and uniqueness retain their full strength
--   - encoding: well-definedness of b, J and the spectral law preceding the moment lemma → unit normalization, self-adjointness, norm bound, probability, support, representation, uniqueness and integrability stated as conclusions in the same item; reason: these are the source definition guarantees; making them explicit rules out all fallback or nonintegrable branches
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Definition 3.1 and Lemma 3.2, pp.13–14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_2 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖bumpVector‖ = 1 ∧ IsSelfAdjoint multiplicationOperator ∧
    IsSelfAdjoint (hardOperator ε) ∧ ‖hardOperator ε‖ ≤ 1 ∧
    IsProbabilityMeasure (hardMeasure ε) ∧
    hardMeasure ε (Set.Icc (-1) 1)ᶜ = 0 ∧
    (∀ f : ℝ → ℂ, Continuous f → Integrable f (hardMeasure ε) ∧
      (∫ h, f h ∂hardMeasure ε) =
        inner ℂ bottomVector (complexRealCalculus f (hardOperator ε) bottomVector)) ∧
    (∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (-1) 1)ᶜ = 0 →
      (∀ f : ℝ → ℂ, Continuous f → Integrable f μ ∧
        (∫ h, f h ∂μ) = inner ℂ bottomVector
          (complexRealCalculus f (hardOperator ε) bottomVector)) → μ = hardMeasure ε) ∧
    Integrable (fun h : ℝ => h) (hardMeasure ε) ∧
    Integrable (fun h : ℝ => h ^ 2) (hardMeasure ε) ∧
    (∫ h : ℝ, h ∂hardMeasure ε) = 0 ∧
    (∫ h : ℝ, h ^ 2 ∂hardMeasure ε) = ε ^ 2 := by sorry

end HamLocality237.Testing
