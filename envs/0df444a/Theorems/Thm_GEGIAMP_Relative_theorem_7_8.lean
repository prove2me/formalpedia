-- Prove2me | Theorems.Thm_GEGIAMP_Relative_theorem_7_8
-- name    : GEGIAMP.Relative.theorem_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:52:34.974783+00:00
-- url     : https://prove2.me/theorems/74977c76-8df7-467c-9d7c-16de28a38b76
-- title:
--   Theorem 7.8 — Euler–Maruyama with exact drift integrals
-- statement:
--   Under (7.25) — $h\le\tau$ and $hL_\tau^3/\tau\le c_0$ for a sufficiently small universal $c_0$ — the recursion $Y^r$ with exact drift integrals $\Gamma_k=\int_{t_k}^{t_{k+1}}\gamma$, $F^r=\sum_ka(t_k,Y^r_k)G_k/\rho^r_k$ and $\mathcal E^r=\mathbb E[W_TF^r]$ of (7.14)–(7.16) satisfy $\|F^r-m(T,Y^r_K)\|_2\le K(\sqrt hL_\tau+hL_\tau^4/\sqrt\tau)$ (7.79) and $P^*-\mathcal E^r\le K(\tau^{3/2}\sqrt{L_\tau}+hL_\tau^3+hL_\tau^4/\sqrt\tau)$ (7.80). The first bound also controls $\|\mathrm{dist}(F^r,[-1,1])\|_2$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - generalization: the grid t_k = kh, 0 ≤ k ≤ K, with T = Kh = 1 − τ and τ the cutoff of (6.1) (τ ∈ (0, 1/2]) → every τ ∈ (0, 1) and every number of cells K ≥ 1, h = (1 − τ)/K; reason: (7.25) is the only condition the theorem states; the grid of (6.1)–(6.2) is an instance (τ ≤ 1/2, K = B m_f)
--   - encoding: Brownian increments G_k = W_{t_{k+1}} − W_{t_k} → the coordinates of g ∼ ⊗_{k<K} N(0, h); ‖·‖₂ is eLpNorm(·, 2) under that law; reason: the same joint law; eLpNorm is ∞ for a non-square-integrable variable, so no junk value
--   - encoding: universal c₀ and K → ∃ c₀, C > 0 before every grid; reason: explicit constants
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Theorem 7.8, p. 31

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Scalar

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Theorem 7.8** (Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 31). Under (7.25) — `h ≤ τ` and `h L_τ³/τ ≤ c₀` for a
sufficiently small universal `c₀` — the exact-drift Euler–Maruyama recursion (7.14)–(7.16) on
the uniform grid `t_k = k h`, `K h = T = 1 − τ`, satisfies
`‖F^r − m(T, Y^r_K)‖₂ ≤ K(√h L_τ + h L_τ⁴/√τ)` (7.79) and
`P* − E^r ≤ K(τ^{3/2} √L_τ + h L_τ³ + h L_τ⁴/√τ)` (7.80); the first bound also controls
`‖dist(F^r, [−1, 1])‖₂`. -/
theorem theorem_7_8 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ (τ : ℝ) (K : ℕ), 0 < τ → τ < 1 → 1 ≤ K →
        let h := (1 - τ) / K
        let Γ : ℕ → ℝ := fun k => ∫ s in ((k : ℝ) * h)..(((k : ℝ) + 1) * h), gam γ s
        let ρr := rhoOf (mF W γ) (aF W γ) h Γ K
        let Fr : (Fin K → ℝ) → ℝ := fun g => Ms (mF W γ) (aF W γ) h Γ ρr g K
        let mT : (Fin K → ℝ) → ℝ := fun g => mF W γ (1 - τ) (Ys (mF W γ) h Γ g K)
        h ≤ τ → h * Lg τ ^ 3 / τ ≤ c₀ →
          eLpNorm (fun g => Fr g - mT g) 2 (gaussLaw K h) ≤
              ENNReal.ofReal (C * (Real.sqrt h * Lg τ + h * Lg τ ^ 4 / Real.sqrt τ)) ∧
          Pstar W γ - corrE (mF W γ) (aF W γ) h Γ K ≤
              C * (τ ^ (3 / 2 : ℝ) * Real.sqrt (Lg τ) + h * Lg τ ^ 3 +
                h * Lg τ ^ 4 / Real.sqrt τ) ∧
          eLpNorm (fun g => distI (Fr g)) 2 (gaussLaw K h) ≤
              ENNReal.ofReal (C * (Real.sqrt h * Lg τ + h * Lg τ ^ 4 / Real.sqrt τ)) := by sorry

end GEGIAMP.Relative
