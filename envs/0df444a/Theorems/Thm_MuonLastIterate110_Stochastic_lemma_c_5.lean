-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_c_5
-- name    : MuonLastIterate110.Stochastic.lemma_c_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:23.532223+00:00
-- url     : https://prove2.me/theorems/48e419a6-ebf8-4c6f-bd9d-7cbac6a45e5f
-- title:
--   Lemma C.5 — noise filtering and momentum tracking
-- statement:
--   Suppose Assumption 3.1 and the noise model (5.3) hold, $J\ge1$ is finite, $\varepsilon\ge0$, and the polynomial schedules (5.4) are used, $\eta_t=\eta_0t^{-p}$, $\beta_t=1-\alpha_0t^{-q}$ with $\eta_0>0$, $0<\alpha_0\le1$, $0<q<1$ and $p>q$. Let $e_t=M_t-g_t$ and $r_t=N_t-g_t$. For $\theta_t=1$ (every $t$) or $\theta_t=\beta_t$ (every $t$),
--
--   $$
--   \mathbb E\|e_t\|=O\bigl(t^{-q/2}+t^{q-p}\bigr),\qquad \mathbb E\|r_t\|=O\bigl(t^{-q/2}+t^{q-p}\bigr).
--   $$
--
--   In particular, the exponent conditions (5.5), $\tfrac34<p\le1$ and $2(1-p)<q<2p-1$, imply
--
--   $$
--   \sum_{t=1}^\infty\eta_t\,\mathbb E\|r_t\|<\infty .
--   $$
--
--   The first term is the noise averaged over the effective memory $t^q$ of the momentum; the second is the lag from tracking a moving gradient. Their balance is what makes the schedule admissible.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals in $[0,\infty]$, so the bounds also assert finiteness. Each $O(\cdot)$ is an explicit constant valid for all sufficiently large $t$.
--
--   Differences from the source:
--
--   - encoding: E[ζ_t | F_{t−1}] = 0 and E[‖ζ_t‖² | F_{t−1}] ≤ σ² in (5.3) → the same conditions plus integrability of ζ_t and of ‖ζ_t‖²; reason: Mathlib's conditional expectation of a non-integrable function is 0; the source's conditional expectations presuppose integrability (the conditional second-moment bound gives E‖ζ_t‖² ≤ σ²)
--   - encoding: E‖e_t‖, E‖r_t‖ and O(·) as t → ∞ → lower Lebesgue integrals in [0, ∞]; ∃ K, eventually ≤ K · (t^{−q/2} + t^{q−p}); (C.22) as a [0, ∞]-valued sum ≠ ∞; reason: nonnegative quantities; this is the definition of O(·) and of a finite series
--   - encoding: real m×n matrices with Frobenius norm ‖X‖_F and inner product tr(XᵀY) → EuclideanSpace ℝ (Fin m × Fin n), read as a matrix through toMat for the products of (3.4); reason: the Euclidean norm and inner product on this type are exactly the Frobenius ones (checked in the sanity file); same instances
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.24, Lemma C.5, (C.20)–(C.22); proof pp.24–25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

open Filter MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic

/-- Lemma C.5 (Noise filtering and momentum tracking), p.24. Under Assumption 3.1, the noise
model (5.3) and the polynomial schedules (5.4) with `η₀ > 0`, `0 < α₀ ≤ 1`, `0 < q < 1` and
`p > q`, for a finite `J ≥ 1`, `ε ≥ 0`, and `θ_t = 1` for every `t` or `θ_t = β_t` for every `t`,
the errors `e_t = M_t − g_t` and `r_t = N_t − g_t` satisfy, as `t → ∞` with constants independent
of `t`,
(C.20) `E‖e_t‖ = O(t^{−q/2} + t^{q−p})`, (C.21) `E‖r_t‖ = O(t^{−q/2} + t^{q−p})`,
and, in particular, under (5.5) — `3/4 < p ≤ 1`, `2(1−p) < q < 2p−1` — (C.22)
`∑_{t ≥ 1} η_t E‖r_t‖ < ∞`. Expectations are lower Lebesgue integrals in `[0, ∞]`. -/
theorem lemma_c_5 {m n : ℕ} (S : Muon m n) (L Finf : ℝ) (hF : Assumption31 S.F L Finf)
    (hJ : 1 ≤ S.J) (hε : 0 ≤ S.ε)
    (η₀ p α₀ q : ℝ) (hη₀ : 0 < η₀) (hα₀ : 0 < α₀) (hα₀' : α₀ ≤ 1) (hq : 0 < q) (hq' : q < 1)
    (hpq : q < p) (hsched : S.PolySchedule η₀ p α₀ q) (hθ : S.ThetaChoice)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (ζ : ℕ → Ω → Mat m n) (σ : ℝ) (hnoise : NoiseModel S μ ℱ ζ σ) :
    (∃ K : ℝ, ∀ᶠ t : ℕ in atTop,
        ∫⁻ ω, ‖S.e (fun s => ζ s ω) t‖ₑ ∂μ
          ≤ ENNReal.ofReal (K * ((t : ℝ) ^ (-q / 2) + (t : ℝ) ^ (q - p)))) ∧
    (∃ K : ℝ, ∀ᶠ t : ℕ in atTop,
        ∫⁻ ω, ‖S.r (fun s => ζ s ω) t‖ₑ ∂μ
          ≤ ENNReal.ofReal (K * ((t : ℝ) ^ (-q / 2) + (t : ℝ) ^ (q - p)))) ∧
    (3 / 4 < p → p ≤ 1 → 2 * (1 - p) < q → q < 2 * p - 1 →
        (∑' t : ℕ, ENNReal.ofReal (S.η (t + 1)) *
            ∫⁻ ω, ‖S.r (fun s => ζ s ω) (t + 1)‖ₑ ∂μ) ≠ ∞) := by sorry

end MuonLastIterate110.Stochastic
