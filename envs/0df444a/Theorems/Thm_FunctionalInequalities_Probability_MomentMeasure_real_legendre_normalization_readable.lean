-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_real_legendre_normalization_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:16.972453+00:00
-- url     : https://prove2.me/theorems/c3394fe1-6941-4e93-a4a1-c77d84338af6
-- title:
--   Real Representative Normalization
-- statement:
--   This is a normalization lemma for a finite real representative of a Legendre transform.
--
--   Let $E$ be a real inner-product space with Borel measurable structure, let $dx$ be a measure, let $q:E\to\overline{\mathbb{R}}$, and let $\psi:E\to\mathbb{R}$. Assume
--
--   $$
--   q^*(x)=\psi(x)\quad\text{in }\overline{\mathbb{R}}\text{ for every }x,
--   $$
--
--   and
--
--   $$
--   \operatorname{mass}_{dx}(q^*)=1.
--   $$
--
--   Then $e^{-\psi}$ is Bochner integrable with respect to $dx$, its integral is one, and the weighted measure `weightedMeasure dx (fun x => (ψ x : EReal))` is a probability measure:
--
--   $$
--   \int e^{-\psi(x)}\,dx=1.
--   $$
--
--   The declaration converts the finite extended-real conjugate mass into real integrability and probability normalization.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem real_legendre_normalization
--       (dx : Measure E) (q : E → EReal) (ψ : E → ℝ)
--       (hψ : ∀ x, legendre q x = (ψ x : EReal))
--       (hmass : mass dx (legendre q) = 1) :
--       Integrable (fun x => Real.exp (-ψ x)) dx ∧
--       (∫ x, Real.exp (-ψ x) ∂dx) = 1 ∧
--       IsProbabilityMeasure (weightedMeasure dx (fun x => (ψ x : EReal)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`log_sub_ge_of_integral_limits`](https://prove2.me/theorems/8c2c9203-7701-486b-b236-68a42ba9b8b5).
--
--   [Source excerpt, lines 268–274](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L268-L274) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L264-L304 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open MeasureTheory Set Metric
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_readable
    (dx : Measure E) (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal))
    (hmass : mass dx (legendre q) = 1) :
    Integrable (fun x => Real.exp (-ψ x)) dx ∧
    (∫ x, Real.exp (-ψ x) ∂dx) = 1 ∧
    IsProbabilityMeasure (weightedMeasure dx (fun x => (ψ x : EReal))) := by sorry
