-- Prove2me | Theorems.Thm_OAI_RadialTransition_gibbs_bogoliubov
-- name    : OAI.RadialTransition.gibbs_bogoliubov
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:45.07001+00:00
-- url     : https://prove2.me/theorems/b89ac6c7-2754-43fe-97f0-d051450dc45d
-- title:
--   Gibbs–Bogoliubov inequality: log Z_E − log Z_F ≤ ⟨F − E⟩ under the Boltzmann measure of E
-- statement:
--   Let $\mu$ be a measure on a measurable space $X$, and let $E, F : X \to \mathbb{R}$ be energies with $E$ measurable (`hE`). Assume:
--   - $e^{-E}$ and $e^{-F}$ are $\mu$-integrable (`hiE`, `hiF`);
--   - the partition functions $Z_E = \int e^{-E}\,d\mu$ and $Z_F = \int e^{-F}\,d\mu$ are positive (`hpE`, `hpF`).
--
--   Let $\gamma_E = Z_E^{-1}\, e^{-E}\mu$ be the Boltzmann probability measure of $E$. In Lean this is `(ENNReal.ofReal (∫ x, Real.exp (-E x) ∂μ))⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x)))`. Assume $F - E$ is $\gamma_E$-integrable (`hi`). Then
--   $$\log Z_E - \log Z_F \;\le\; \int (F - E)\, d\gamma_E .$$
--
--   This is the Gibbs–Bogoliubov inequality: the free energy $-\log Z_F$ is at most $-\log Z_E + \langle F - E\rangle_E$. It is Jensen's inequality for the exponential, applied to $\int e^{-(F-E)}\,d\gamma_E = Z_F/Z_E$.
--
--   Lean: `OAI.RadialTransition.gibbs_bogoliubov`. This is OpenAI's lemma `log_boltzmann_difference_le` in `lean/OAI/Probability/RadialTransition/BoltzmannMeasure.lean`, with OpenAI's definitions `boltzmannPartition` and `boltzmannMeasure` written out, so that the statement uses only Mathlib.
-- source:
--   The Gibbs–Bogoliubov inequality (Bogoliubov's variational principle for the free energy; see R. P. Feynman, Statistical Mechanics: A Set of Lectures, W. A. Benjamin, 1972). Lean proof: OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/BoltzmannMeasure.lean (declaration OAI.RadialTransition.log_boltzmann_difference_le, stated here with its two definitions written out)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem gibbs_bogoliubov {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E F : X → ℝ} (hE : Measurable E)
    (hiE : Integrable (fun x => Real.exp (-E x)) μ)
    (hiF : Integrable (fun x => Real.exp (-F x)) μ)
    (hpE : 0 < ∫ x, Real.exp (-E x) ∂μ) (hpF : 0 < ∫ x, Real.exp (-F x) ∂μ)
    (hi : Integrable (fun x => F x - E x)
      ((ENNReal.ofReal (∫ x, Real.exp (-E x) ∂μ))⁻¹ •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x))))) :
    Real.log (∫ x, Real.exp (-E x) ∂μ) - Real.log (∫ x, Real.exp (-F x) ∂μ) ≤
      ∫ x, F x - E x ∂((ENNReal.ofReal (∫ x, Real.exp (-E x) ∂μ))⁻¹ •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x)))) := by
  sorry

end RadialTransition

end

end OAI
end
