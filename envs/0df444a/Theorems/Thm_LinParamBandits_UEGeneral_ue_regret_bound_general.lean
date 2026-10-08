-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_ue_regret_bound_general
-- name    : LinParamBandits.UEGeneral.ue_regret_bound_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:30.980241+00:00
-- url     : https://prove2.me/theorems/a3d34a10-e33a-4db8-8510-bb0acf68cc2b
-- title:
--   Theorem 4.1 — UE regret ≤ a₄r‖z‖ + a₅r√T log^{3/2} T and Risk ≤ a₄r E‖Z‖ + a₅r√T log^{3/2} T
-- statement:
--   **Theorem 4.1 (Bounds for General Compact Sets of Arms).** For all constants $\sigma_0, \bar u, \lambda_0 > 0$ there are constants $a_4, a_5 > 0$, depending only on $\sigma_0, \bar u, \lambda_0$, with the following property. For every dimension $r \ge 2$, every compact nonempty set of arms $\mathcal U_r \subset \mathbb R^r$, every noise model and arms $b_1, \dots, b_r$ satisfying Assumption 1 with these constants, every run of the Uncertainty Ellipsoid policy, and every horizon $T \ge r+1$:
--
--   1. for every $z \in \mathbb R^r$,
--   $$\mathrm{Regret}(z, T, \mathrm{UE}) \le a_4\,r\,\|z\| + a_5\,r\sqrt T\log^{3/2}T;$$
--   2. for every prior distribution of $Z$ with $\mathbb E\|Z\| < \infty$, the regret is integrable in $z$ and
--   $$\mathrm{Risk}(T, \mathrm{UE}) \le a_4\,r\,\mathbb E\big[\|Z\|\big] + a_5\,r\sqrt T\log^{3/2}T.$$
--
--   The UE policy thus comes within a factor $\log^{3/2}T$ of the $\Omega(r\sqrt T)$ lower bound of Theorem 2.1, for any compact set of arms, without knowing the horizon $T$.
--
--   **Formalization Note** The quantifier order is the paper's: $a_4, a_5$ are chosen after $\sigma_0, \bar u, \lambda_0$ and before $r$, the arm set, the noise kernel, the arms $b_k$, the UE run, $T$ and $z$. Finite arm sets are included. $\log^{3/2}T$ is the real power `Real.log T ^ (3/2 : ℝ)`, with $\log T > 0$ since $T \ge 3$. The prior $\mu$ is a probability measure on $\mathbb R^r$; $\mathbb E\|Z\| < \infty$ is stated as integrability of $\|z\|$ (the bound mentions $\mathbb E\|Z\|$), and integrability of $z \mapsto \mathrm{Regret}(z, T, \mathrm{UE})$ is part of the conclusion, so the risk is never a junk value. The noise is independent of $Z$, so the risk is the integral over the prior of the regret given $Z = z$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem 4.1, p. 21 (proof App. B.2, p. 39)

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Theorem 4.1 (p. 21): bounds for general compact sets of arms. The constants `a₄, a₅`
depend only on `σ₀, ū, λ₀`: they are chosen before `r`, the arm set, the noise, the UE run,
`T` and `z`. -/
theorem ue_regret_bound_general :
    ∀ σ₀ ubar lam0 : ℝ, 0 < σ₀ → 0 < ubar → 0 < lam0 →
    ∃ a₄ a₅ : ℝ, 0 < a₄ ∧ 0 < a₅ ∧
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)), IsCompact 𝒰 → 𝒰.Nonempty →
    ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν →
    ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), Assumption1 𝒰 ν b σ₀ ubar lam0 →
    ∀ (ψ : Policy r), IsUE 𝒰 b σ₀ ubar lam0 ψ →
    ∀ (T : ℕ), r + 1 ≤ T →
      (∀ z : LinParamBandits.LowerBound.Vec r,
        regret ν 𝒰 ψ z T ≤
          a₄ * r * ‖z‖ + a₅ * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ)) ∧
      (∀ μ : Measure (LinParamBandits.LowerBound.Vec r), IsProbabilityMeasure μ → Integrable (fun z => ‖z‖) μ →
        Integrable (fun z => regret ν 𝒰 ψ z T) μ ∧
        risk ν 𝒰 ψ μ T ≤
          a₄ * r * (∫ z, ‖z‖ ∂μ) + a₅ * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ)) := by sorry

end LinParamBandits.UEGeneral
