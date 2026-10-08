-- Prove2me | Theorems.Thm_OnlineLearningOCO_OnlineToBatch_round_identity
-- name    : OnlineLearningOCO.OnlineToBatch.round_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:50.108714+00:00
-- url     : https://prove2.me/theorems/c3c3969e-8524-41f0-83ba-838e504ea8f8
-- title:
--   §5, p. 188 — the online loss of round t is unbiased for the risk of w_t
-- statement:
--   Let $\psi_0,\dots,\psi_{T-1}$ be independent examples, each with law $Q$, let $c$ be an admissible cost on $S\times\Psi$ with risk $C(w) = \mathbb E_{\psi\sim Q}[c(w,\psi)]$, and let $w_t = A_t(\psi_0,\dots,\psi_{t-1}) \in S$ be the prediction of an online learner in round $t$. Then for every round $t$,
--   $$\mathbb E\big[c(w_t,\psi_t)\big] = \mathbb E\big[C(w_t)\big].$$
--
--   This is the step of the proof of Theorem 5.1 where the non-anticipation of the online algorithm enters: $w_t$ is a function of the earlier examples only, and $\psi_t$ is a fresh draw from $Q$.
--
--   **Formalization Note** Rounds are numbered from $0$. No integrability of $c(w_t,\psi_t)$ is assumed; both sides are Bochner integrals of nonnegative functions.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 188, §5, proof of Theorem 5.1, display after (5.2)

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- Shalev-Shwartz, FnT ML 4(2) (2011), §5, proof of Theorem 5.1, display after (5.2), p. 188.
Let `ψ₀, …, ψ_{T-1}` be i.i.d. with law `Q`, and let `w_t` be the prediction of a
non-anticipating online algorithm in round `t` of the online-to-batch conversion. Then
`𝔼[c(w_t, ψ_t)] = 𝔼[C(w_t)]`. -/
theorem round_identity {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    {T : ℕ} (t : Fin T) :
    ∫ ψ, c (iterate A ψ t) (ψ t) ∂(sampleLaw Q T) =
      ∫ ψ, risk Q c (iterate A ψ t) ∂(sampleLaw Q T) := by sorry

end OnlineLearningOCO.OnlineToBatch
