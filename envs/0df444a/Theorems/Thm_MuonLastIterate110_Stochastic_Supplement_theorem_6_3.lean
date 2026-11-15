-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_Supplement_theorem_6_3
-- name    : MuonLastIterate110.Stochastic.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:41:15.084631+00:00
-- url     : https://prove2.me/theorems/0aaa0f8d-3afc-4cfb-ba8c-b946a334cb79
-- title:
--   Theorem 6.3 — density-one gradient rates for finite-step Muon
-- statement:
--   There are two independent regimes, always using the published finite-step Muon run on real matrices, its true gradient $g_t=\nabla F(W_t)$, and Definition 6.2 for $o_{\mathrm{dens}}$.
--
--   1. Suppose Assumption 3.1 holds: $F$ is continuously differentiable, bounded below by $F_{\inf}$, and has $L$-Lipschitz gradient with $L>0$. Use exact gradients, $J\ge1$, $\varepsilon>0$, constant $\beta\in[0,1)$, $\theta\in[0,1]$, and $0<\eta\le\varepsilon(1-\beta)/(4Lu_J)$, from arbitrary deterministic $W_1,M_0$. Then, pathwise,
--
--   $$
--   \|g_t\|=o_{\mathrm{dens}}(t^{-1/2}).
--   $$
--
--   2. Suppose the hypotheses of Theorem 5.2 hold: Assumption 3.1, finite $J\ge1$, $\varepsilon\ge0$, deterministic initialization and schedules $\eta_t=\eta_0t^{-p}$, $\beta_t=1-\alpha_0t^{-q}$ with $\eta_0>0$, $0<\alpha_0\le1$, $3/4<p\le1$, $2(1-p)<q<2p-1$, and either $\theta_t=1$ for all $t$ or $\theta_t=\beta_t$ for all $t$. On a probability space with filtration $(\mathcal F_t)$, the states $W_t,M_{t-1}$ are $\mathcal F_{t-1}$-measurable, and $G_t=g_t+\zeta_t$ satisfies $\mathbb E[\zeta_t\mid\mathcal F_{t-1}]=0$ and $\mathbb E[\|\zeta_t\|^2\mid\mathcal F_{t-1}]\le\sigma^2$ for some real $\sigma$. If additionally $p<1$, then almost surely, path by path,
--
--   $$
--   \|g_t\|=\begin{cases}
--   o_{\mathrm{dens}}(t^{-(1-p)/2}),&\varepsilon>0,\\
--   o_{\mathrm{dens}}(t^{-(1-p)}),&\varepsilon=0.
--   \end{cases}
--   $$
--
--   These rates quantify the gradient norm outside an exceptional set of iterations of natural density zero, without asserting a pointwise rate. Both clauses are retained in one theorem, each universally quantified over its own run and initialization.
--
--   Differences from the source:
--
--   - encoding: real m×n matrices with Frobenius norm → the published EuclideanSpace ℝ (Fin m × Fin n) carrier and Muon recursion; reason: its norm is the Frobenius norm; no matrix or initial condition is excluded
--   - encoding: the fixed-step setting of §4 with imposed condition (4.2) → FixedStep S L β θ η, with the exact-gradient run driven by ζ ≡ 0 where specified; reason: unfolding gives precisely J ≥ 1, ε > 0, the stated parameter ranges, schedule equalities for t ≥ 1, and the same non-strict step bound
--   - encoding: the notation o_dens of Definition 6.2 → DensityOne with real powers of the positive integer time; reason: the predicate counts exactly the printed exceedance set for every c > 0; time zero never affects the asymptotic limit
--   - encoding: the assumptions of Theorem 5.2 and (5.3) → the same published Assumption31, PolySchedule, ThetaChoice, probability measure, filtration, and NoiseModel, with the additional p < 1 printed in Theorem 6.3; reason: NoiseModel makes integrability explicit as required for the source conditional expectations, avoiding the default value of non-integrable conditional expectation; no new noise restriction is imposed
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.13, Theorem 6.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_DensityOne
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_FixedStep

open Filter Topology MeasureTheory
open scoped ENNReal

namespace MuonLastIterate110.Stochastic.Supplement

/-- Theorem 6.3, p.13: the deterministic clause and both stochastic rate regimes.
The two clauses quantify independently over their own runs and initial conditions. -/
theorem theorem_6_3 :
    (∀ {m n : ℕ} (S : Muon m n) (L Finf β θ η : ℝ)
    (hF : Assumption31 S.F L Finf) (hfixed : FixedStep S L β θ η),
      DensityOne (fun t => ‖S.g (fun _ => 0) t‖)
        (fun t => (t : ℝ) ^ (-(1 : ℝ) / 2))) ∧
    (∀ {m n : ℕ} (S : Muon m n) (L Finf : ℝ)
      (hF : Assumption31 S.F L Finf) (hJ : 1 ≤ S.J) (hε : 0 ≤ S.ε)
      (η₀ p α₀ q : ℝ) (hη₀ : 0 < η₀) (hα₀ : 0 < α₀) (hα₀' : α₀ ≤ 1)
      (hp : 3 / 4 < p) (hp' : p ≤ 1) (hq : 2 * (1 - p) < q) (hq' : q < 2 * p - 1)
      (hsched : S.PolySchedule η₀ p α₀ q) (hθ : S.ThetaChoice) (hpless : p < 1)
      {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ mΩ) (ζ : ℕ → Ω → Mat m n) (σ : ℝ) (hnoise : NoiseModel S μ ℱ ζ σ),
      ∀ᵐ ω ∂μ,
        (0 < S.ε → DensityOne (fun t => ‖S.g (fun s => ζ s ω) t‖)
          (fun t => (t : ℝ) ^ (-(1 - p) / 2))) ∧
        (S.ε = 0 → DensityOne (fun t => ‖S.g (fun s => ζ s ω) t‖)
          (fun t => (t : ℝ) ^ (-(1 - p))))) := by sorry

end MuonLastIterate110.Stochastic.Supplement
