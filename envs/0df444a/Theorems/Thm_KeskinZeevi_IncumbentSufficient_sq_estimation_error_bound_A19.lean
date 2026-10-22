-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_sq_estimation_error_bound_A19
-- name    : KeskinZeevi.IncumbentSufficient.sq_estimation_error_bound_A19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:46:05.111459+00:00
-- url     : https://prove2.me/theorems/7a6a9ea1-b638-434f-b840-b3f52e30a92d
-- title:
--   (A19) — squared estimation error of the greedy deviation
-- statement:
--   Consider the incumbent price model with light-tailed shocks of variance $\sigma^2$, a slope $\beta \in \mathfrak B$ with $\psi(\beta) \ne 0$, a constant $\kappa_1 > 0$ and a start time $t_0 \ge 1$. Set
--   $$K_0 = \frac{\hat D^2}{4 b_{\max}^4}, \qquad K_1 = 512\, K_0\, \sigma^2 (u-l)^2 (\psi(\beta))^{-4}, \qquad K_2 = 4(u-l)^2 .$$
--   There is a period $N$ such that every pricing policy satisfying condition (ii) of Theorem 4 from $t_0$ on, i.e. almost surely $\sum_{s=1}^t (\psi(b_s) - x_{s+1})^2 \le \kappa_1 \log t$ for all $t \ge t_0$, obeys for every $t \ge N$
--   $$\mathbb E^\pi_\beta(\psi(\beta) - \psi(b_t))^2 \le K_1 t^{-1} + K_2\, \mathbb P^\pi_\beta(A_t^c).$$
--   The estimation error of the greedy deviation thus decays like $1/t$, up to the probability that the greedy prices were not already close to optimal.
--
--   **Formalization Note.** The paper states (A19) "for any time period $t \ge N(\beta)$" with $N(\beta) = \max\{N_0(\beta), 5\}$ and $N_0(\beta)$ an unspecified threshold. Here $N$ is existential and chosen before the policy, so it is uniform in $\pi$, as in the paper, where $N_0(\beta)$ depends only on $\psi(\beta)$ and $\kappa_1$. It may also depend on $t_0$. $K_0$, $K_1$, $K_2$ are the explicit constants of p. 1160. $K_0 = \max_{b \in \mathfrak B} (\psi'(b))^2 = \hat D^2/(4 b_{\max}^4)$. The start time $t_0$ is the same convention as in the goal theorem. $\mathbb P(A_t^c)$ enters as a real number (`toReal`).
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1160, Appendix A.3, proof of Theorem 4, Eq. (A19) (constants K_0, K_1, K_2, N(β) on pp. 1159-1160)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1160, (A19): fix `β ∈ 𝔅` with `ψ(β) ≠ 0`, `κ₁ > 0` and a start time
`t₀ ≥ 1`. There is `N` (the paper's `N(β)`) such that for every policy satisfying condition (ii)
of Theorem 4, `Σ_{s=1}^t (ψ(b_s) - x_{s+1})² ≤ κ₁ log t` almost surely for all `t ≥ t₀`, and
every `t ≥ N`,
`E(ψ(β) - ψ(b_t))² ≤ K₁ t⁻¹ + K₂ P(A_tᶜ)` with `K₀ = D̂²/(4 b_max⁴)`,
`K₁ = 512 K₀ σ² (u - l)² ψ(β)⁻⁴` and `K₂ = 4 (u - l)²`. -/
theorem sq_estimation_error_bound_A19 (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (β : ℝ) (hβ : β ∈ M.B) (hψ : M.psi β ≠ 0)
    (κ₁ : ℝ) (hκ₁ : 0 < κ₁) (t₀ : ℕ) (ht₀ : 1 ≤ t₀) :
    ∃ N : ℕ, ∀ π : Policy M,
      (∀ᵐ ω ∂P, ∀ t : ℕ, t₀ ≤ t →
        ∑ s ∈ Finset.Icc 1 t, (M.psi (truncEst π β ε s ω) - dev π β ε (s + 1) ω) ^ 2 ≤
          κ₁ * Real.log t) →
      ∀ t : ℕ, N ≤ t →
        ∫ ω, (M.psi β - M.psi (truncEst π β ε t ω)) ^ 2 ∂P ≤
          512 * (M.DHat ^ 2 / (4 * M.bMax ^ 4)) * σ ^ 2 * (M.u - M.l) ^ 2 / M.psi β ^ 4 / t +
            4 * (M.u - M.l) ^ 2 * (P (goodEvent π β ε t)ᶜ).toReal := by sorry

end KeskinZeevi.IncumbentSufficient
