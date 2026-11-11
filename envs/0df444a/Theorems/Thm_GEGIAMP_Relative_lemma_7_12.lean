-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_7_12
-- name    : GEGIAMP.Relative.lemma_7_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:52:22.684736+00:00
-- url     : https://prove2.me/theorems/b39a732f-82db-4da9-abd6-23dbd6f6aa68
-- title:
--   Lemma 7.12 — effect of fixed normalization factors
-- statement:
--   Let $0<\nu\le1/2$ and let $\omega$ be deterministic with $1/2\le\omega_k\le2$ and $\max_{k<K}|\omega_k^2/\rho_k^2-1|\le\nu$ (7.116). With $M^\omega$, $M^\rho$ from (6.7)–(6.8) on the same increments, $\|M^\omega_K-M^\rho_K\|_2^2=\sum_{k<K}h(\rho_k/\omega_k-1)^2\le K\nu^2$ (7.117). Consequently replacing $\rho$ by $\omega$ changes $\|M^\rho_K-m(T,Y_K)\|_2$ and $\|\mathrm{dist}(M^\rho_K,[-1,1])\|_2$ by at most $K\nu$, and the correlation $\mathcal E=\mathbb E[W_TM^\rho_K]$ by at most $K\nu$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - generalization: the quadrature coefficients Γ^q_k of (6.6) on the grid of (6.1)–(6.2) (Kh = T ≤ 1) → any deterministic coefficients Γc, any h > 0 and K with Kh < 1; reason: the proof uses only the martingale structure of (6.8) and Kh ≤ 1; the algorithm’s grid and Γ^q are an instance
--   - encoding: "changes … by at most Kν" → two one-sided inequalities between eLpNorms (each ≤ the other + Cν) and |E[W_T M^ω_K] − E| ≤ Cν; reason: the same statement without real-valued junk for infinite norms
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 7.12, p. 37

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Scalar

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 7.12** (effect of fixed normalization factors; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 37). Let
`0 < ν ≤ 1/2` and let `ω` be a deterministic vector with `1/2 ≤ ω_k ≤ 2`,
`max_{k<K} |ω_k²/ρ_k² − 1| ≤ ν` (7.116). With `M^ω`, `M^ρ` from (6.7)–(6.8) on the same
increments, `‖M^ω_K − M^ρ_K‖₂² = ∑_{k<K} h(ρ_k/ω_k − 1)² ≤ Kν²` (7.117); replacing `ρ` by `ω`
changes `‖M^ρ_K − m(T, Y_K)‖₂` and `‖dist(M^ρ_K, [−1,1])‖₂` by at most `Kν`, and the correlation
`E = E[W_T M^ρ_K]` by at most `Kν`. -/
theorem lemma_7_12 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (K : ℕ) (Γc ω : ℕ → ℝ) (ν : ℝ), 0 < h → (K : ℝ) * h < 1 → 0 < ν → ν ≤ 1 / 2 →
        let ρ := rhoOf (mF W γ) (aF W γ) h Γc K
        Cond7116 ω ρ ν K →
        let μ := gaussLaw K h
        let Mω : (Fin K → ℝ) → ℝ := fun g => Ms (mF W γ) (aF W γ) h Γc ω g K
        let Mρ : (Fin K → ℝ) → ℝ := fun g => Ms (mF W γ) (aF W γ) h Γc ρ g K
        let mT : (Fin K → ℝ) → ℝ := fun g => mF W γ ((K : ℝ) * h) (Ys (mF W γ) h Γc g K)
        -- (7.117)
        eLpNorm (fun g => Mω g - Mρ g) 2 μ ^ 2 =
            ENNReal.ofReal (∑ k ∈ Finset.range K, h * (ρ k / ω k - 1) ^ 2) ∧
        (∑ k ∈ Finset.range K, h * (ρ k / ω k - 1) ^ 2) ≤ C * ν ^ 2 ∧
        -- the terminal norm changes by at most Cν
        eLpNorm (fun g => Mω g - mT g) 2 μ ≤ eLpNorm (fun g => Mρ g - mT g) 2 μ + ENNReal.ofReal (C * ν) ∧
        eLpNorm (fun g => Mρ g - mT g) 2 μ ≤ eLpNorm (fun g => Mω g - mT g) 2 μ + ENNReal.ofReal (C * ν) ∧
        -- the clipping norm changes by at most Cν
        eLpNorm (fun g => distI (Mω g)) 2 μ ≤ eLpNorm (fun g => distI (Mρ g)) 2 μ + ENNReal.ofReal (C * ν) ∧
        eLpNorm (fun g => distI (Mρ g)) 2 μ ≤ eLpNorm (fun g => distI (Mω g)) 2 μ + ENNReal.ofReal (C * ν) ∧
        -- the correlation changes by at most Cν
        |(∫ g, WT g * Mω g ∂μ) - corrE (mF W γ) (aF W γ) h Γc K| ≤ C * ν := by sorry

end GEGIAMP.Relative
