-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_sum_integral_spectral_noise_energy_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:22.090826+00:00
-- url     : https://prove2.me/theorems/581326c3-8b69-482f-9883-e185292234e7
-- title:
--   Spectral Noise Energy Bound
-- statement:
--   This is a finite-dimensional matrix-energy estimate with the trace bound supplied as a hypothesis.
--
--   Let $\rho$ and $\gamma$ be probability measures on measurable spaces $\Omega$ and $\Delta$. Let $H:\Omega\to\mathbb R^{n\times n}$ have measurable entries, be symmetric almost everywhere, have integrable entries, and have mean $I$. Assume that for every symmetric matrix $B$, $\operatorname{tr}(BH B H)$ is integrable and
--   $$\int\operatorname{tr}(BH(y)BH(y))\,d\rho(y)\le 2\operatorname{tr}(B^2).$$
--   Let $M$ be symmetric and invertible, and let $t\in\mathbb R$. Define $B=\sqrt{M^2}$, $S=\sqrt B$, and $Q=\operatorname{sign}(M)$. Then each coordinate energy is integrable and
--
--   $$\sum_i\int_{\Omega\times\Delta}\left\|(SH(y)S+tI)Qe_i\right\|^2\,d(\rho\otimes\gamma)
--   \le 2\operatorname{tr}(M^2)+2t\operatorname{tr}(B)+nt^2.$$
--
--   No log-concavity or Stein-kernel conclusion is part of the statement; the trace estimate is an input.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem sum_integral_spectral_noise_energy_le {n : ℕ} {Ω Δ : Type*}
--       [MeasurableSpace Ω] [MeasurableSpace Δ] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
--       (γ : Measure Δ) [IsProbabilityMeasure γ]
--       (H : Ω → Matrix (Fin n) (Fin n) ℝ)
--       (hHmeas : ∀ i j, Measurable (fun y => H y i j))
--       (hHsym : ∀ᵐ y ∂ρ, (H y).IsSymm)
--       (hHint : ∀ i j, Integrable (fun y => H y i j) ρ)
--       (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
--       (hT25 : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
--         Integrable (fun y => Matrix.trace (B*H y*B*H y)) ρ ∧
--           (∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) ≤ 2*Matrix.trace (B*B))
--       (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) (t : ℝ) :
--       let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
--       let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
--       let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
--       (∀ i : Fin n, Integrable (fun y => ‖action (S*H y*S + t • 1)
--         (action Q (EuclideanSpace.single i 1))‖^2) ρ) ∧
--       (∑ i : Fin n, ∫ p : Ω × Δ, ‖action (S*H p.1*S + t • 1)
--         (action Q (EuclideanSpace.single i 1))‖^2 ∂ρ.prod γ) ≤
--         2*Matrix.trace (M*M) + 2*t*Matrix.trace B + (n : ℝ)*t^2
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Stein/QuadraticAction`](https://prove2.me/theorems/0e4b9766-8959-44c6-bfc8-ee388e8834ba).
--
--   Definition modules: [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Supporting theorems: [`integral_trace_mul_of_mean_one`](https://prove2.me/theorems/0fa1db57-6ad5-4665-9a1e-3a5d91a7bc2b), [`symmetric_matrix_spectral_geometry`](https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010).
--
--   [Source excerpt, lines 66–86](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean#L66-L86) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean#L66-L145 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Stein.QuadraticAction`, declaration `FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace MatrixOrder
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.LogConcave.sum_integral_spectral_noise_energy_le_readable {n : ℕ} {Ω Δ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Δ] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (γ : Measure Δ) [IsProbabilityMeasure γ]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hHmeas : ∀ i j, Measurable (fun y => H y i j))
    (hHsym : ∀ᵐ y ∂ρ, (H y).IsSymm)
    (hHint : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hT25 : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      Integrable (fun y => Matrix.trace (B*H y*B*H y)) ρ ∧
        (∫ y, Matrix.trace (B*H y*B*H y) ∂ρ) ≤ 2*Matrix.trace (B*B))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) (t : ℝ) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    (∀ i : Fin n, Integrable (fun y => ‖action (S*H y*S + t • 1)
      (action Q (EuclideanSpace.single i 1))‖^2) ρ) ∧
    (∑ i : Fin n, ∫ p : Ω × Δ, ‖action (S*H p.1*S + t • 1)
      (action Q (EuclideanSpace.single i 1))‖^2 ∂ρ.prod γ) ≤
      2*Matrix.trace (M*M) + 2*t*Matrix.trace B + (n : ℝ)*t^2 := by sorry
