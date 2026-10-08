-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_ue_regret_bound_finite
-- name    : LinParamBandits.UEFinite.ue_regret_bound_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:29.237992+00:00
-- url     : https://prove2.me/theorems/f02a0dce-e069-4dcd-a645-0b3c0f984a09
-- title:
--   Theorem 4.2 — for finitely many arms, UE has regret ≤ a₆|𝒰_r|‖z‖ + a₇|𝒰_r| Σ_u min{log T/Δ^u(z), TΔ^u(z)} and risk ≤ a₈|𝒰_r|E‖Z‖ + a₉|𝒰_r|² log² T
-- statement:
--   **Theorem 4.2 (Bounds for Finitely Many Arms).** Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis: a finite nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ with $r \ge 2$, rewards $X_t = U_t'Z + W_t$, and Assumption 1 with parameters $\sigma_0, \bar u, \lambda_0$. Let $\Delta^u(z) = \max_{v \in \mathcal U_r} v'z - u'z$.
--
--   1. There are positive constants $a_6, a_7$ depending only on $\sigma_0, \bar u, \lambda_0$ such that for every $r$, every such arm set and noise, every run of the Uncertainty Ellipsoid policy, every $T \ge r + 1$ and every $z \in \mathbb R^r$,
--   $$\mathrm{Regret}(z, T, \mathrm{UE}) \le a_6|\mathcal U_r|\,\|z\| + a_7|\mathcal U_r|\sum_{u \in \mathcal U_r}\min\Big\{\frac{\log T}{\Delta^u(z)}, T\Delta^u(z)\Big\}.$$
--   2. Suppose moreover that for some $M_0 > 0$ and every arm $u$, the law of $\Delta^u(Z)$ under the prior consists of a point mass at $0$ and a density bounded above by $M_0$ on $\mathbb R_+$. Then there are positive constants $a_8, a_9$ depending only on $\sigma_0, \bar u, \lambda_0, M_0$ such that for every $T \ge r + 1$,
--   $$\mathrm{Risk}(T, \mathrm{UE}) \le a_8|\mathcal U_r|\,\mathbb E[\|Z\|] + a_9|\mathcal U_r|^2\log^2 T.$$
--
--   For a fixed set of arms the regret thus grows like $\log T$, within a constant factor of the Lai–Robbins lower bound, and the Bayes risk like $\log^2 T$.
--
--   **Formalization Note** The constants are chosen after $\sigma_0, \bar u, \lambda_0$ (and $M_0$) and before the dimension $r$, the arm set, the noise, the tie-breaking rule, $T$, $z$ and the prior. For an optimal arm ($\Delta^u(z) = 0$) the summand $\min\{\log T/0, 0\}$ is $0$, which is also Lean's value. In the risk part the prior is a probability measure with $\mathbb E\|Z\| < \infty$ (otherwise the bound is vacuous), and the conclusion includes the integrability of $z \mapsto \mathrm{Regret}(z, T, \mathrm{UE})$. $\log^2 T$ is $(\log T)^2$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem 4.2, pp. 21–22

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem ue_regret_bound_finite :
    (∀ σ₀ ū lam₀ : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ →
      ∃ a₆ a₇ : ℝ, 0 < a₆ ∧ 0 < a₇ ∧
        ∀ (r : ℕ), 2 ≤ r → ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite), 𝒰.Nonempty →
        ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν → NoiseAssumption 𝒰 ν σ₀ →
        ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), ArmAssumption 𝒰 b ū lam₀ →
        ∀ (ψ : LinParamBandits.UEGeneral.Policy r), IsUE 𝒰 b σ₀ ū lam₀ ψ →
        ∀ (T : ℕ), r + 1 ≤ T → ∀ z : LinParamBandits.LowerBound.Vec r,
          Regret 𝒰 ν ψ z T ≤
            a₆ * (𝒰.ncard : ℝ) * ‖z‖ +
              a₇ * (𝒰.ncard : ℝ) *
                ∑ u ∈ h𝒰fin.toFinset, min (Real.log T / gap 𝒰 u z) (T * gap 𝒰 u z)) ∧
    (∀ σ₀ ū lam₀ M₀ : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < M₀ →
      ∃ a₈ a₉ : ℝ, 0 < a₈ ∧ 0 < a₉ ∧
        ∀ (r : ℕ), 2 ≤ r → ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)), 𝒰.Finite → 𝒰.Nonempty →
        ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν → NoiseAssumption 𝒰 ν σ₀ →
        ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), ArmAssumption 𝒰 b ū lam₀ →
        ∀ (ψ : LinParamBandits.UEGeneral.Policy r), IsUE 𝒰 b σ₀ ū lam₀ ψ →
        ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
          (∫⁻ z, (‖z‖₊ : ENNReal) ∂μ) < ⊤ → (∀ u ∈ 𝒰, GapDensityLe 𝒰 μ M₀ u) →
        ∀ (T : ℕ), r + 1 ≤ T →
          Integrable (fun z => Regret 𝒰 ν ψ z T) μ ∧
          Risk 𝒰 ν ψ μ T ≤
            a₈ * (𝒰.ncard : ℝ) * ∫ z, ‖z‖ ∂μ + a₉ * (𝒰.ncard : ℝ) ^ 2 * Real.log T ^ 2) := by sorry

end LinParamBandits.UEFinite
