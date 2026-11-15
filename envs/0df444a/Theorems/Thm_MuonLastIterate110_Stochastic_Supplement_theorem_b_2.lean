-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_Supplement_theorem_b_2
-- name    : MuonLastIterate110.Stochastic.Supplement.theorem_b_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:41:41.134231+00:00
-- url     : https://prove2.me/theorems/adc3960e-5782-44df-bbb5-fef3fdc3c14e
-- title:
--   Theorem B.2 — fixed-step stationarity with square-summable errors
-- statement:
--   Let $F:\mathbb R^{m\times n}\to\mathbb R$ satisfy Assumption 3.1: continuous differentiability, lower bound $F_{\inf}$, and $L$-Lipschitz gradient with $L>0$. Use the published Muon recursion with $G_t=g_t+\zeta_t$, $g_t=\nabla F(W_t)$, finite $J\ge1$, $\varepsilon>0$, constant $\beta\in[0,1)$, $\theta\in[0,1]$, and $0<\eta\le\varepsilon(1-\beta)/(4Lu_J)$, from arbitrary deterministic $W_1,M_0$. Here $u_J$ is the maximum amplification of the fixed Newton–Schulz polynomial, $D_t$ is the update direction, and $M_t$ is the momentum. All norms are Frobenius norms.
--
--   For every perturbation sequence satisfying
--
--   $$
--   \sum_{t=1}^\infty\|\zeta_t\|^2<\infty,
--   $$
--
--   one has, pathwise,
--
--   $$
--   \sum_{t=1}^\infty\|D_t\|^2<\infty,\qquad
--   \sum_{t=1}^\infty\|M_t-g_t\|^2<\infty,\qquad
--   \sum_{t=1}^\infty\|g_t\|^2<\infty,
--   $$
--
--   and in particular $\|g_t\|\to0$. If instead the perturbations are random variables on a probability space and
--
--   $$
--   \sum_{t=1}^\infty\mathbb E\|\zeta_t\|^2<\infty,
--   $$
--
--   then all three series and the resulting gradient convergence hold almost surely, and
--
--   $$
--   \mathbb E\|\nabla F(W_t)\|^2\longrightarrow0.
--   $$
--
--   This extends the fixed-step theorem to finite total squared perturbation energy. Neither conditional unbiasedness nor independence is required, and no deterministic decay envelope is imposed.
--
--   **Formalization Note** Nonnegative expectations and their series are valued in $[0,\infty]$, using lower integrals, so the finite expected-energy hypothesis has its literal mathematical meaning.
--
--   Differences from the source:
--
--   - encoding: real m×n matrices with Frobenius norm → the published EuclideanSpace ℝ (Fin m × Fin n) carrier and Muon recursion; reason: its norm is the Frobenius norm; no matrix or initial condition is excluded
--   - encoding: the fixed-step setting of §4 with imposed condition (4.2) → FixedStep S L β θ η, with the exact-gradient run driven by ζ ≡ 0 where specified; reason: unfolding gives precisely J ≥ 1, ε > 0, the stated parameter ranges, schedule equalities for t ≥ 1, and the same non-strict step bound
--   - encoding: finite series of nonnegative squared norms indexed from t = 1 → Summable of the squared-norm sequences at index t + 1; reason: for nonnegative real terms this is equivalent to finiteness of the series and omits only the unused time zero
--   - reading: random perturbations → measurable perturbation maps on an arbitrary probability space, applied to the recursion path by path; reason: the source random perturbations are random variables; this is the same measurable-map convention as the published Theorem C.1, with no filtration, independence or unbiasedness
--   - encoding: Σ E‖ζ_t‖² < ∞ and E‖∇F(W_t)‖² → 0 → a sum of lower integrals in [0, ∞] different from ∞ and convergence of the gradient-square lower integrals to zero; reason: nonnegative expectations are extended Lebesgue integrals, so non-integrability cannot create a zero expectation
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.18, Theorem B.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_FixedStep

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic.Supplement

/-- Theorem B.2, p.18: arbitrary square-summable perturbations, and random perturbations
of summable expected squared norm. No filtration, unbiasedness or independence is imposed. -/
theorem theorem_b_2 {m n : ℕ} (S : Muon m n) (L Finf β θ η : ℝ)
    (hF : Assumption31 S.F L Finf) (hfixed : FixedStep S L β θ η) :
    (∀ ζ : ℕ → Mat m n, Summable (fun t : ℕ => ‖ζ (t + 1)‖ ^ 2) →
      (Summable (fun t : ℕ => ‖S.D ζ (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.e ζ (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.g ζ (t + 1)‖ ^ 2) ∧
    Tendsto (fun t => ‖S.g ζ t‖) atTop (𝓝 0))) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ζ : ℕ → Ω → Mat m n), (∀ t, Measurable (ζ t)) →
      (∑' t : ℕ, ∫⁻ ω, ENNReal.ofReal (‖ζ (t + 1) ω‖ ^ 2) ∂μ) ≠ ∞ →
      (∀ᵐ ω ∂μ,
        Summable (fun t : ℕ => ‖S.D (fun s => ζ s ω) (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.e (fun s => ζ s ω) (t + 1)‖ ^ 2) ∧
    Summable (fun t : ℕ => ‖S.g (fun s => ζ s ω) (t + 1)‖ ^ 2) ∧
    Tendsto (fun t => ‖S.g (fun s => ζ s ω) t‖) atTop (𝓝 0)) ∧
      Tendsto (fun t => ∫⁻ ω, ENNReal.ofReal (‖S.g (fun s => ζ s ω) t‖ ^ 2) ∂μ)
        atTop (𝓝 0)) := by sorry

end MuonLastIterate110.Stochastic.Supplement
