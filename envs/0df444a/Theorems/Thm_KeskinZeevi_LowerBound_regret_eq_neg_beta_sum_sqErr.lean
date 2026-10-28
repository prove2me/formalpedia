-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_regret_eq_neg_beta_sum_sqErr
-- name    : KeskinZeevi.LowerBound.regret_eq_neg_beta_sum_sqErr
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:43:35.301281+00:00
-- url     : https://prove2.me/theorems/291db0d6-d156-4669-a4bd-326e0853ac7f
-- title:
--   Regret equals −β times the cumulative squared pricing error
-- statement:
--   In the single-product linear-demand model with i.i.d. Gaussian demand shocks, fix a pricing policy $\pi$. Two statements hold.
--
--   First, for every $\theta = (\alpha,\beta) \in \Theta$ and every horizon $T$,
--   $$\Delta^\pi_\theta(T) = \sum_{t=1}^T \mathbb{E}^\pi_\theta\big[r^*_\theta - r_\theta(p_t)\big] = -\beta \sum_{t=1}^T \mathbb{E}^\pi_\theta(p_t-\varphi(\theta))^2 .$$
--
--   Second, because $\beta \le b_{\max} < 0$ on $\Theta$, for every horizon $T$,
--   $$\Delta^\pi(T) \;\ge\; |b_{\max}|\, \sup_{\theta\in\Theta}\Big\{\sum_{t=2}^T \mathbb{E}^\pi_\theta(p_t-\varphi(\theta))^2\Big\}.$$
--
--   Together these form the regret display in the proof of Theorem 1, which turns bounds on pricing errors into bounds on regret.
--
--   **Formalization Note.** The identity $r^*_\theta - r_\theta(p) = -\beta(p-\varphi(\theta))^2$ uses $\beta \ne 0$, so the first clause is stated for $\theta \in \Theta$. Paper periods $1,\dots,T$ are Lean periods $0,\dots,T-1$. Paper periods $2,\dots,T$ are Lean periods $1,\dots,T-1$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1156, Appendix A.1, proof of Theorem 1, display following (A2)

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- The regret display in the proof of Theorem 1 (Keskin and Zeevi 2014, §A.1, p. 1156):
for every `θ = (α, β) ∈ Θ` and horizon `T`,
`Δ^π_θ(T) = Σ_{t=1}^T E^π_θ[r*_θ − r_θ(p_t)] = −β Σ_{t=1}^T E^π_θ(p_t − φ(θ))²`, and hence
`Δ^π(T) ≥ |b_max| sup_{θ∈Θ} Σ_{t=2}^T E^π_θ(p_t − φ(θ))²`. Paper periods `1, …, T` are Lean
periods `0, …, T − 1`; paper periods `2, …, T` are Lean periods `1, …, T − 1`. -/
theorem regret_eq_neg_beta_sum_sqErr (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (hε : GaussianNoise M.σ P ε)
    (π : Policy M.l M.u) :
    (∀ θ ∈ M.Θ, ∀ T : ℕ,
        regret P ε π θ T = -θ.2 * ∑ t ∈ Finset.range T, sqErr P ε π θ t) ∧
      ∀ T : ℕ,
        |M.bMax| * ⨆ θ : M.Θ, ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t
          ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.LowerBound
