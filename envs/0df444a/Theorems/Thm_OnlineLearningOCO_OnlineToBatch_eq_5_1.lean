-- Prove2me | Theorems.Thm_OnlineLearningOCO_OnlineToBatch_eq_5_1
-- name    : OnlineLearningOCO.OnlineToBatch.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:51.202685+00:00
-- url     : https://prove2.me/theorems/5ca7d2eb-d4b0-47cd-8b26-633cca8475aa
-- title:
--   Equation (5.1) — the expected average online loss equals the expected average risk of the iterates
-- statement:
--   Let $T\ge1$, let $\psi_0,\dots,\psi_{T-1}$ be independent examples, each with law $Q$, let $c$ be an admissible cost on $S\times\Psi$ with risk $C$, and let $w_0,\dots,w_{T-1}$ be the predictions of an online learner run on the losses $f_t(w)=c(w,\psi_t)$, where $w_t$ depends only on $\psi_0,\dots,\psi_{t-1}$. Then
--   $$\mathbb E\Big[\frac1T\sum_{t} C(w_t)\Big] = \mathbb E\Big[\frac1T\sum_{t} c(w_t,\psi_t)\Big].$$
--
--   The average online loss, which the regret of the online algorithm controls, is thus an unbiased estimate of the average risk of the iterates.
--
--   **Formalization Note** Rounds are numbered $0,\dots,T-1$. No integrability of the online losses is assumed.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 188, §5, proof of Theorem 5.1, Equation (5.1)

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- Equation (5.1) (Shalev-Shwartz, FnT ML 4(2) (2011), §5, proof of Theorem 5.1, p. 188).
For an i.i.d. sample `ψ₀, …, ψ_{T-1}` with law `Q` and the predictions `w_t` of a
non-anticipating online algorithm,
`𝔼[(1/T) ∑_t C(w_t)] = 𝔼[(1/T) ∑_t c(w_t, ψ_t)]`. -/
theorem eq_5_1 {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    (T : ℕ) (hT : 0 < T) :
    ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t) ∂(sampleLaw Q T) =
      ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, c (iterate A ψ t) (ψ t) ∂(sampleLaw Q T) := by sorry

end OnlineLearningOCO.OnlineToBatch
