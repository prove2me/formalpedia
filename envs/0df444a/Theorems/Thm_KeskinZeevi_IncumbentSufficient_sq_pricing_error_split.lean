-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentSufficient_sq_pricing_error_split
-- name    : KeskinZeevi.IncumbentSufficient.sq_pricing_error_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:45:43.150171+00:00
-- url     : https://prove2.me/theorems/90a61b50-f4e2-4d84-8bf3-a14b9f7f862b
-- title:
--   (A14) — splitting the squared pricing error
-- statement:
--   For every pricing policy, every slope $\beta \in \mathfrak B$ and every period $t \ge 1$, let $b_t$ be the truncated least squares estimate at the end of period $t$. Then the expected squared distance between the next deviation $x_{t+1}$ and the optimal deviation $\psi(\beta)$ splits as
--   $$\mathbb E^\pi_\beta(\psi(\beta) - x_{t+1})^2 \le 2\,\mathbb E^\pi_\beta(\psi(\beta) - \psi(b_t))^2 + 2\,\mathbb E^\pi_\beta(\psi(b_t) - x_{t+1})^2 .$$
--   The first term is the estimation error of the greedy deviation, and the second is the policy's departure from the greedy deviation, which condition (ii) of Theorem 4 controls.
--
--   **Formalization Note.** Expectations are integrals over the noise space. All three integrands are bounded (prices lie in $[l,u]$ and $b_t \in \mathfrak B$) and measurable. The statement is required for $t \ge 1$, where $b_t$ is computed from data.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1159, Appendix A.3, proof of Theorem 4, Eq. (A14)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
open RobustBooking.Shared

open MeasureTheory ProbabilityTheory

namespace KeskinZeevi.IncumbentSufficient

/-- Keskin–Zeevi 2014, p. 1159, (A14): for every policy, every `β ∈ 𝔅` and every `t ≥ 1`,
`E(ψ(β) - x_{t+1})² ≤ 2 E(ψ(β) - ψ(b_t))² + 2 E(ψ(b_t) - x_{t+1})²`, where `b_t` is the truncated
least squares estimate at the end of period `t`. All integrands are bounded and measurable. -/
theorem sq_pricing_error_split (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (β : ℝ) (hβ : β ∈ M.B)
    (t : ℕ) (ht : 1 ≤ t) :
    ∫ ω, (M.psi β - dev π β ε (t + 1) ω) ^ 2 ∂P ≤
      2 * ∫ ω, (M.psi β - M.psi (truncEst π β ε t ω)) ^ 2 ∂P +
        2 * ∫ ω, (M.psi (truncEst π β ε t ω) - dev π β ε (t + 1) ω) ^ 2 ∂P := by sorry

end KeskinZeevi.IncumbentSufficient
