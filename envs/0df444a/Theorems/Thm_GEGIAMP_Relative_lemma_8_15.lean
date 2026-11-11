-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_8_15
-- name    : GEGIAMP.Relative.lemma_8_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:55:14.824623+00:00
-- url     : https://prove2.me/theorems/7a112e25-f948-454b-8e85-8970866d441b
-- title:
--   Lemma 8.15 — the empirical clipping loss
-- statement:
--   For fixed $\omega$ satisfying (7.116), put $\overline V=1+V$ and $\mathfrak s=\|M^\omega_K-m(T,Y_K)\|_2$, and let $b_0$ be as in (8.71). If $h\Lambda(T)\le1$, then for $t_{\rm dev}\ge1$, with failure at most $e^{-t_{\rm dev}}$, $\|f-\mathrm{clip}(f,[-1,1]^N)\|^2/N\le4(\mathfrak s+b_0)^2+2b_0^2+K\overline Vt_{\rm dev}/N$ (8.82). At the chosen scalar parameters, $b_0=o(\varepsilon)$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: b_0 "as in (8.71)" with its universal constant K, and the K of (8.82) → ∃ K_b > 0 and C > 0 before all parameters; reason: universal constants
--   - reading: V of (8.27) with its constant K_x; ν, grid and K_R as in §§6–8 → every K_x > 0 with 4a² ≤ K_x Λ; ν = c_ν ε/log(4d) for any c_ν > 0; any positive κ with K_R as in (6.5); 0 < ε ≤ 1; reason: as in Lemma 8.13
--   - reading: the construction of §8 (with the final query appended) → hypothesis d ≤ N; reason: §8 states once (p. 39) that this construction requires d ≤ N
--   - encoding: "b_0 = o(ε) at the chosen scalar parameters" → ∀ δ > 0 ∃ ε₁ > 0 ∀ 0 < ε ≤ ε₁, b_0(ε) ≤ δ ε, for the fixed constants; reason: the definition of o(ε) as ε → 0
--   - encoding: 𝔰 = ‖M^ω_K − m(T, Y_K)‖₂ → the real number (eLpNorm … 2).toReal; reason: a finite norm is unchanged; an infinite one would read as 0, which only makes the bound harder
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 8.15, pp. 57–58

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 8.15** (the empirical clipping loss; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, pp. 57–58). For fixed `ω`
satisfying (7.116), put `V̄ = 1 + V` and `s = ‖M^ω_K − m(T, Y_K)‖₂`, and let `b_0` be as in
(8.71). If `hΛ(T) ≤ 1`, then for `t_dev ≥ 1`, with failure at most `e^{−t_dev}`,
`‖f − clip(f, [−1,1]^N)‖²/N ≤ 4(s + b_0)² + 2b_0² + K V̄ t_dev/N` (8.82). At the chosen scalar
parameters, `b_0 = o(ε)`. -/
theorem lemma_8_15 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos)
    (hKR : KRValid W γ κ) (cν : ℝ) (hcν : 0 < cν) (Kx : ℝ) (hKx0 : 0 < Kx)
    (hKx : ∀ t x : ℝ, 0 ≤ t → t < 1 → 4 * aF W γ t x ^ 2 ≤ Kx * Lam t) :
    ∃ Kb C : ℝ, 0 < Kb ∧ 0 < C ∧
      (∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        let P := params κ ε
        let Γc := Gq (gam γ) κ ε
        let ρ := rhoOf (mF W γ) (aF W γ) P.h Γc P.K
        ∀ (ω : ℕ → ℝ), Cond7116 ω ρ (nuOf cν ε P.d) P.K →
        let s := (eLpNorm (fun g => Ms (mF W γ) (aF W γ) P.h Γc ω g P.K -
            mF W γ P.T (Ys (mF W γ) P.h Γc g P.K)) 2 (gaussLaw P.K P.h)).toReal
        let b0 := b0Of Kb κ ε
        P.h * Lam P.T ≤ 1 →
        ∀ (tdev : ℝ) (N : ℕ), 1 ≤ tdev → P.d ≤ N →
          matLaw N P {x | ¬ (
            let f := fvec (mF W γ) (aF W γ) P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2)
            vnorm (fun i => f i - clipVec f i) ^ 2 / N ≤
              4 * (s + b0) ^ 2 + 2 * b0 ^ 2 + C * Vbar Kx P * tdev / N)} ≤
            ENNReal.ofReal (Real.exp (-tdev))) ∧
      -- b₀ = o(ε) at the chosen parameters
      (∀ δ : ℝ, 0 < δ → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → b0Of Kb κ ε ≤ δ * ε) := by sorry

end GEGIAMP.Relative
