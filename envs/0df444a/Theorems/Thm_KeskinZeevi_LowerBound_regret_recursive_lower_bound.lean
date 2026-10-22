-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_regret_recursive_lower_bound
-- name    : KeskinZeevi.LowerBound.regret_recursive_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:43:49.297637+00:00
-- url     : https://prove2.me/theorems/074b0cf0-5d83-4c57-b76e-2356c9dbca51
-- title:
--   (A3) — recursive lower bound on worst-case regret
-- statement:
--   In the single-product linear-demand model with parameter set $\Theta$, slopes in $[b_{\min}, b_{\max}]$ with $b_{\max}<0$, and i.i.d. $\mathcal{N}(0,\sigma^2)$ demand shocks, there exist finite positive constants $c_0$ and $c_1$ such that, for every pricing policy $\pi$ and every horizon $T$,
--   $$\Delta^\pi(T) \;\ge\; b_{\max}^2 \sum_{t=2}^T \frac{c_0}{|b_{\max}|\,c_1 + \Delta^\pi(t-1)} .$$
--   This is inequality (A3). It bounds the worst-case regret at horizon $T$ from below by a sum involving the worst-case regret at earlier horizons. Solving the recursion gives $\Delta^\pi(T) \ge c\sqrt{T}$.
--
--   **Formalization Note.** $c_0, c_1$ depend only on the model and are chosen before the noise, the policy and the horizon. In the paper they are the constants of Lemma 1; here they are existential. The sum index is $k = t-1 \in \{1,\dots,T-1\}$, and `worstRegret … k` is $\Delta^\pi(k)$. The denominators are positive because regret is nonnegative.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1156, Appendix A.1, proof of Theorem 1, Eq. (A3)

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- Inequality (A3) (Keskin and Zeevi 2014, §A.1, p. 1156): there are finite positive constants
`c₀, c₁`, depending only on the model, such that for every Gaussian noise sequence, every policy
`π` and every horizon `T`,
`Δ^π(T) ≥ b_max² Σ_{t=2}^T c₀ / (|b_max| c₁ + Δ^π(t − 1))`.
Paper periods `t = 2, …, T` are indexed by `t − 1 ∈ {1, …, T − 1}` in Lean, and
`worstRegret … k` is the paper's `Δ^π(k)`. -/
theorem regret_recursive_lower_bound.{u} (M : Model) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        M.bMax ^ 2 * ∑ k ∈ Finset.Ico 1 T,
            c₀ / (|M.bMax| * c₁ + worstRegret M P ε π k)
          ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.LowerBound
