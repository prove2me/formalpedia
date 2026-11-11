-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_fact_2_27
-- name    : JainCRERepetition.Cubic.fact_2_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:51.310915+00:00
-- url     : https://prove2.me/theorems/2e4a87a4-8e11-4b62-9484-282ccd622bfe
-- title:
--   Fact 2.27 — four-matrix trace inequality and variational formulas
-- statement:
--   The function $\beta_0(s)=\pi/[2(\cosh(\pi s)+1)]$ is a nonnegative probability density on the real line. For Hermitian $H_1,H_2,H_3,H_4$,
--
--   $$\operatorname{Tr}e^{H_1+H_2+H_3+H_4}\le\int_{\mathbb R}\beta_0(s)\operatorname{Tr}\bigl[e^{H_1}e^{(1+is)H_2/2}e^{(1+is)H_3/2}e^{H_4}e^{(1-is)H_3/2}e^{(1-is)H_2/2}\bigr]ds.$$
--
--   For a density $\alpha$ and positive definite $\zeta$, the variational functionals defined in the module equal $(\ln2)D(\alpha\|\zeta)$ and $(\ln2)D_M(\alpha\|\zeta)$, respectively; no normalization of $\zeta$ is required. The measured formula also holds for singular normalized $\zeta$. Measured relative entropy is lower semicontinuous on pairs of normalized states. This supplies the support-general matrix tool for Lemma 4.2.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 21, Fact 2.27; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_variational

open scoped ComplexOrder MatrixOrder BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

theorem fact_2_27 :
    (∀ s : ℝ, 0 ≤ beta0 s) ∧ MeasureTheory.Integrable beta0 ∧ (∫ s : ℝ, beta0 s) = 1 ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (H1 H2 H3 H4 : Op I),
      H1.IsHermitian → H2.IsHermitian → H3.IsHermitian → H4.IsHermitian →
      (hermitianExp (H1+H2+H3+H4) 1).trace.re ≤
        ∫ s : ℝ, beta0 s *
          (hermitianExp H1 1 * hermitianExp H2 ((1+Complex.I*(s:ℂ))/2) *
            hermitianExp H3 ((1+Complex.I*(s:ℂ))/2) * hermitianExp H4 1 *
            hermitianExp H3 ((1-Complex.I*(s:ℂ))/2) *
            hermitianExp H2 ((1-Complex.I*(s:ℂ))/2)).trace.re) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (α ζ : Op I),
      IsState α → ζ.PosDef →
      (Real.log 2 : EReal) * D α ζ = variationalD α ζ ∧
      (Real.log 2 : EReal) * MeasuredD α ζ = variationalMeasuredD α ζ) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I],
      (∀ α ζ : Op I, IsState α → IsState ζ →
        (Real.log 2 : EReal) * MeasuredD α ζ = variationalMeasuredD α ζ) ∧
      LowerSemicontinuousOn (fun z : Op I × Op I => MeasuredD z.1 z.2)
        {z | IsState z.1 ∧ IsState z.2}) := by sorry

end JainCRERepetition.Cubic
