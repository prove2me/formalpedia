-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_full_sequence_stationarity
-- name    : MuonLastIterate110.Stochastic.full_sequence_stationarity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:14.930596+00:00
-- url     : https://prove2.me/theorems/fabbad67-24be-4fec-93c2-594884110c1f
-- title:
--   Theorem 5.2 — full-sequence stationarity of finite-step Muon under persistent noise
-- statement:
--   Let $F:\mathbb R^{m\times n}\to\mathbb R$ satisfy Assumption 3.1, and run finite-step Muon (3.1)–(3.3) from deterministic $W_1,M_0$ with a finite number $J\ge1$ of quintic Newton–Schulz steps and stabilizer $\varepsilon\ge0$. Suppose the gradient noise satisfies (5.3) for a filtration to which $W_t,M_{t-1}$ are adapted at time $t-1$:
--
--   $$
--   \mathbb E[\zeta_t\mid\mathcal F_{t-1}]=0,\qquad\mathbb E[\|\zeta_t\|^2\mid\mathcal F_{t-1}]\le\sigma^2\quad\text{a.s.}
--   $$
--
--   Use the schedules
--
--   $$
--   \eta_t=\eta_0t^{-p},\quad\beta_t=1-\alpha_0t^{-q},\quad\eta_0>0,\ 0<\alpha_0\le1,\qquad \tfrac34<p\le1,\quad 2(1-p)<q<2p-1,
--   $$
--
--   with either $\theta_t=1$ for every $t$ or $\theta_t=\beta_t$ for every $t$. Then, with $g_t=\nabla F(W_t)$,
--
--   $$
--   \|g_t\|\to0\ \text{a.s.},\qquad\mathbb E\|g_t\|^2\to0, \tag{5.6}
--   $$
--
--   and
--
--   $$
--   \sum_{t=1}^\infty\eta_t\psi_\varepsilon(\|g_t\|)<\infty,\qquad\sum_{t=1}^\infty\eta_t\|g_t\|^2<\infty\quad\text{a.s.} \tag{5.7}
--   $$
--
--   The guarantees hold on the entire admissible range $3/4<p\le1$, including $p=1$, for every $\varepsilon\ge0$ including $\varepsilon=0$, and for both ordinary momentum and the Nesterov-style mixture used in practice.
--
--   The theorem shows that persistent, non-decaying gradient noise does not prevent the current iterate of practical finite-step Muon from becoming stationary, provided the learning rate decreases and the momentum coefficient tends to one at coordinated polynomial rates.
--
--   **Formalization Note** $\mathbb E\|g_t\|^2$ is a lower Lebesgue integral in $[0,\infty]$, so the mean-square conclusion cannot hold through a junk value. The noise model also requires $\zeta_t$ and $\|\zeta_t\|^2$ to be integrable, because Mathlib's conditional expectation of a non-integrable function is $0$. The series are indexed from $t=1$.
--
--   Differences from the source:
--
--   - encoding: E[ζ_t | F_{t−1}] = 0 and E[‖ζ_t‖² | F_{t−1}] ≤ σ² in (5.3) → the same conditions plus integrability of ζ_t and of ‖ζ_t‖²; reason: Mathlib's conditional expectation of a non-integrable function is 0; the source's conditional expectations presuppose integrability (the conditional second-moment bound gives E‖ζ_t‖² ≤ σ²)
--   - encoding: E‖g_t‖² → 0; series “< ∞” indexed from t = 1 → lower Lebesgue integral of ‖g_t‖² in [0, ∞] tends to 0; Summable of the shifted nonnegative sequences; reason: nonnegative quantities, so these are the source's statements
--   - encoding: real m×n matrices with Frobenius norm ‖X‖_F and inner product tr(XᵀY) → EuclideanSpace ℝ (Fin m × Fin n), read as a matrix through toMat for the products of (3.4); reason: the Euclidean norm and inner product on this type are exactly the Frobenius ones (checked in the sanity file); same instances
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.10, Theorem 5.2, (5.4)–(5.7), with (5.3) p.9 and the model of §3.1 pp.5–7; proof p.25, §C.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Muon

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic

/-- Theorem 5.2 (Full-sequence stationarity under persistent noise), p.10. Suppose Assumption 3.1
and the noise model (5.3) hold. Fix finite `J ≥ 1` and `ε ≥ 0`; use the schedules (5.4)–(5.5):
`η_t = η₀ t^{−p}`, `β_t = 1 − α₀ t^{−q}` with `η₀ > 0`, `0 < α₀ ≤ 1`, `3/4 < p ≤ 1`,
`2(1 − p) < q < 2p − 1`; and either `θ_t = 1` for every `t` or `θ_t = β_t` for every `t`. Then
(5.6) `‖g_t‖ → 0` a.s. and `E‖g_t‖² → 0`, and
(5.7) `∑_{t ≥ 1} η_t ψ_ε(‖g_t‖) < ∞` and `∑_{t ≥ 1} η_t ‖g_t‖² < ∞` a.s.
`W₁`, `M₀` are arbitrary deterministic points; `E‖g_t‖²` is a lower Lebesgue integral in `[0, ∞]`. -/
theorem full_sequence_stationarity {m n : ℕ} (S : Muon m n) (L Finf : ℝ)
    (hF : Assumption31 S.F L Finf) (hJ : 1 ≤ S.J) (hε : 0 ≤ S.ε)
    (η₀ p α₀ q : ℝ) (hη₀ : 0 < η₀) (hα₀ : 0 < α₀) (hα₀' : α₀ ≤ 1)
    (hp : 3 / 4 < p) (hp' : p ≤ 1) (hq : 2 * (1 - p) < q) (hq' : q < 2 * p - 1)
    (hsched : S.PolySchedule η₀ p α₀ q) (hθ : S.ThetaChoice)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (ζ : ℕ → Ω → Mat m n) (σ : ℝ) (hnoise : NoiseModel S μ ℱ ζ σ) :
    (∀ᵐ ω ∂μ, Tendsto (fun t => ‖S.g (fun s => ζ s ω) t‖) atTop (𝓝 0)) ∧
    Tendsto (fun t => ∫⁻ ω, ENNReal.ofReal (‖S.g (fun s => ζ s ω) t‖ ^ 2) ∂μ) atTop (𝓝 0) ∧
    (∀ᵐ ω ∂μ, Summable (fun t : ℕ => S.η (t + 1) * psi S.ε ‖S.g (fun s => ζ s ω) (t + 1)‖)) ∧
    (∀ᵐ ω ∂μ, Summable (fun t : ℕ => S.η (t + 1) * ‖S.g (fun s => ζ s ω) (t + 1)‖ ^ 2)) := by sorry

end MuonLastIterate110.Stochastic
