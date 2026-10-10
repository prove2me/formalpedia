-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_proposition_3
-- name    : LuoSunLiu.DIP.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:46.338088+00:00
-- url     : https://prove2.me/theorems/6ad1bee2-6fec-49d1-bf11-c4c936d6d021
-- title:
--   Proposition 3, pp. 22–23 — single-episode regret: w.p. ≥ 1 − δ bound, and E(R_{T₀}) ≤ C′₃ log(C′₂T₀)T₀^{2/3} + 4p_max L‖θ̂ − θ₀‖₁T₀
-- statement:
--   Let the standing assumptions of the pricing model hold, let $F$ be $L$-Lipschitz (Assumption 1), and let Assumption 2 hold with constant $C_A$. Consider one episode of Inner Algorithm B with $\beta_t = \beta^*_t$, started at period $1$, with an input estimate $\hat\theta$ satisfying $\|\hat\theta\|_1 \le W$. Write $R_{T_0} = \sum_{t=1}^{T_0} r_t$ for the regret (1).
--
--   1. **High-probability bound.** There is a constant $C > 0$, depending only on the model and $C_A$, such that for every such $\hat\theta$, every $d \ge 1$ with $p_{\max} + 2\|\hat\theta\|_1 < d\,p_{\max}$, every $\lambda > 0$, $\delta \in (0, 1)$, $T_0 \ge 1$ and every run, with probability at least $1 - \delta$,
--   $$R_{T_0} \le 2\sqrt{2dT_0\beta^*_{T_0}\log\frac{d\lambda + T_0p_{\max}^2}{d\lambda}} + 4p_{\max}L\|\hat\theta - \theta_0\|_1T_0 + C\frac{T_0}{d^2} + 2dp_{\max}.$$
--   2. **Expected bound.** For every discretization constant $C_d$ with $p_{\max} + 2W < C_d\,p_{\max}$ and every $\lambda > 0$ there are constants $C'_2, C'_3 > 0$ such that, with $\delta = 1/T_0$ and $d = C_d\lceil T_0^{1/6}\rceil$, for every such $\hat\theta$, every $T_0 \ge 1$ and every run,
--   $$\mathbb E(R_{T_0}) \le C'_3\log(C'_2T_0)\,T_0^{2/3} + 4p_{\max}L\|\hat\theta - \theta_0\|_1T_0 .$$
--
--   Applied to episode $k$ of DIP with $\hat\theta = \hat\theta_{k-1}$, part 2 gives the per-episode bound from which Theorem 1 follows.
--
--   **Formalization Note** The printed statement uses the letter $C$ twice: for the continuous-part constant ($C = C_2C_3^2$, p. 53) and for the discretization constant in $d = C\lceil T_0^{1/6}\rceil$; here they are $C$ and $C_d$. The printed $\tilde O(T_0^{2/3})$ is pinned to $C'_3\log(C'_2T_0)T_0^{2/3}$, the form the proof derives (p. 54). Two hypotheses the proof uses are made explicit: $\|\hat\theta\|_1 \le W$ (the input is a projection onto $\Theta$, p. 53) and $p^*(x) \in (0, p_{\max})$ (part of the standing assumptions). The grid hypothesis ($p_{\max} + 2\|\hat\theta\|_1 < d\,p_{\max}$, resp. $p_{\max} + 2W < C_d\,p_{\max}$) makes every candidate set nonempty. All constants are chosen before $\hat\theta$, the probability space and $T_0$; this uniformity is what the proof gives and what Theorem 1 needs. Expectations are lower Lebesgue integrals of the nonnegative regret.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 22–23, Proposition 3; proof pp. 52–54

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB

open MeasureTheory ProbabilityTheory NNReal

namespace LuoSunLiu.DIP

/-- Proposition 3 (Luo, Sun and Liu, arXiv:2109.07340v2, pp. 22–23; proof pp. 52–54). Under
Assumptions 1–2, for a single episode run of Inner Algorithm B with `β_t = β*_t` and an input
estimate `θ̂` with `‖θ̂‖₁ ≤ W`:
(a) there is a constant `C` (depending only on the model and the constant of Assumption 2) such
that, whenever `p_max + 2‖θ̂‖₁ < d p_max`, `λ > 0`, `δ ∈ (0, 1)` and `T₀ ≥ 1`, with probability at
least `1 - δ`,
`R_{T₀} ≤ 2√(2dT₀β*_{T₀} log((dλ + T₀p²_max)/(dλ))) + 4p_max L‖θ̂ - θ₀‖₁T₀ + C T₀/d² + 2dp_max`;
(b) for every discretization constant `C_d` with `p_max + 2W < C_d p_max` and every `λ > 0`, there
are constants `C′₂, C′₃ > 0` such that with `δ = 1/T₀` and `d = C_d ⌈T₀^{1/6}⌉`,
`E(R_{T₀}) ≤ C′₃ log(C′₂T₀) T₀^{2/3} + 4p_max L‖θ̂ - θ₀‖₁T₀` for every `T₀ ≥ 1` (the `Õ` of the
printed statement, pinned from the proof, p. 54). -/
theorem proposition_3 {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA) :
    (∃ Ccont : ℝ, 0 < Ccont ∧
      ∀ (θh : Fin d0 → ℝ), l1 θh ≤ M.W → ∀ (d : ℕ), 1 ≤ d → M.pmax + 2 * l1 θh < d * M.pmax →
      ∀ (lam δ : ℝ), 0 < lam → δ ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (T0 : ℕ), 1 ≤ T0 →
      (∀ ω, ∃ j : ℕ → Fin d, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
        (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
        ∀ ω ∈ E, cumRegret M x p T0 ω ≤
          2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
            Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
          4 * M.pmax * L * l1 (θh - M.θ0) * T0 + Ccont * T0 / (d : ℝ) ^ 2 +
          2 * d * M.pmax) ∧
    (∀ (Cdisc : ℕ), M.pmax + 2 * M.W < Cdisc * M.pmax → ∀ (lam : ℝ), 0 < lam →
      ∃ C2' C3' : ℝ, 0 < C2' ∧ 0 < C3' ∧
      ∀ (θh : Fin d0 → ℝ), l1 θh ≤ M.W →
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (T0 : ℕ), 1 ≤ T0 →
      (∀ ω, ∃ j : ℕ → Fin (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊),
        IsInnerBRun M.pmax θh lam
          (betaStar M.pmax lam (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊) (1 / (T0 : ℝ))) 0 T0
          (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T0 ω) ∂P ≤
        ENNReal.ofReal (C3' * Real.log (C2' * T0) * (T0 : ℝ) ^ ((2 : ℝ) / 3) +
          4 * M.pmax * L * l1 (θh - M.θ0) * T0)) := by sorry

end LuoSunLiu.DIP
