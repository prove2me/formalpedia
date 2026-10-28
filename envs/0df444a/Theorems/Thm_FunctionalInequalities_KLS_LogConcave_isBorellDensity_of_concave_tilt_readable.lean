-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_concave_tilt_readable
-- name    : FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:28.707363+00:00
-- url     : https://prove2.me/theorems/74db6db5-1902-4308-9adf-57a1e7cc376f
-- title:
--   Borell Density Under a Concave Tilt
-- statement:
--   This states stability of Borell densities under continuous concave tilting.
--
--   Let $E$ be a real inner-product space with Borel measurable structure. Let $\mu$ and $\nu$ be probability measures, let $m$ be a measure, and let $\rho:E\to\mathbb R$ be a Borell density of $\mu$ with respect to $m$. Let $\phi:E\to\mathbb R$ be continuous and concave on all of $E$, and assume
--
--   $$\nu=\mu.\operatorname{tilted}(\phi).$$
--
--   Then $\nu$ has Borell density
--
--   $$x\longmapsto \rho(x)\,\frac{e^{\phi(x)}}{\int_E e^{\phi(y)}\,d\mu(y)}$$
--
--   with respect to $m$. The definition permits zeros of $\rho$. This result is a measure-theoretic closure property for the log-concave class and does not assume finite dimensionality in its Lean type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem isBorellDensity_of_concave_tilt (μ ν : ProbabilityMeasure E)
--       (m : Measure E) {ρ : E → ℝ} (hρ : KLS.IsBorellDensity (μ : Measure E) m ρ)
--       (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
--       (hν : (ν : Measure E) = (μ : Measure E).tilted φ) :
--       KLS.IsBorellDensity (ν : Measure E) m
--         (fun x => ρ x * (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂(μ : Measure E)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/ConcaveTilt`](https://prove2.me/theorems/7ed5056e-c3f4-4ab8-9bf8-55101609725f).
--
--   Definition modules: [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70), [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5).
--
--   Next: [`logConcave_of_concave_tilt`](https://prove2.me/theorems/ec28e166-3e80-4482-a015-77d8598725bc).
--
--   [Source excerpt, lines 40–45](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/ConcaveTilt.lean#L40-L45) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/ConcaveTilt.lean#L38-L77 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt`, declaration `FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_ConcaveTilt

open MeasureTheory Set Filter Topology FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_readable (μ ν : ProbabilityMeasure E)
    (m : Measure E) {ρ : E → ℝ} (hρ : KLS.IsBorellDensity (μ : Measure E) m ρ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) :
    KLS.IsBorellDensity (ν : Measure E) m
      (fun x => ρ x * (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂(μ : Measure E))) := by sorry
