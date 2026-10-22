-- Prove2me | Theorems.Thm_KeskinZeevi_IncumbentLowerBound_regret_eq_neg_beta_sum_sqErr
-- name    : KeskinZeevi.IncumbentLowerBound.regret_eq_neg_beta_sum_sqErr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:03:51.910128+00:00
-- url     : https://prove2.me/theorems/633136c1-dba2-44cc-93e9-6e987317a931
-- title:
--   Proof of Theorem 3, first display on p. 1159 — worst-case regret as the supremum of −β times the cumulative squared pricing error, and its lower bound
-- statement:
--   Consider the incumbent price model with i.i.d. $\mathcal N(0,\sigma^2)$ demand shocks. There exist finite positive constants $c_0$ and $c_1$, depending only on the model, with the following property. For every pricing policy $\pi$ and every horizon $T$,
--   $$\Delta^\pi(T) = \sup_{\beta \in \mathfrak B,\ \psi(\beta) \ne 0} \left\{ -\beta \sum_{t=1}^T \mathbb E^\pi_\beta (x_t - \psi(\beta))^2 \right\} \;\ge\; |b_{\max}| \sum_{t=2}^T \frac{c_0}{c_1 + (u-l)^2 (t-1)}.$$
--   The paper writes the right side as $|b_{\max}| \sup_{\beta \in \mathfrak B,\ \psi(\beta) \ne 0} \sum_{t=2}^T c_0/(c_1 + (u-l)^2(t-1))$; the summand does not depend on $\beta$, so the supremum is the sum itself.
--
--   The equality holds because $r_\beta$ is a quadratic with leading coefficient $\beta$ that is maximized at $\psi(\beta)$, so $r_\beta(\psi(\beta)) - r_\beta(x) = -\beta (x - \psi(\beta))^2$. The inequality follows from $-\beta \ge |b_{\max}|$ for $\beta \in [b_{\min}, b_{\max}]$ and the previous display. It turns the lower bound on cumulative pricing error into a lower bound on regret.
--
--   **Formalization Note.** Lean period $t$ is the paper's period $t+1$. The paper's $\sum_{t=1}^T$ is the Lean sum over `Finset.range T`, and the paper's $\sum_{t=2}^T$ with the term $t-1$ is the Lean sum over $t \in [1, T)$ with the term $t$. The constants are chosen before the probability space, the noise, the policy and the horizon, as in Lemma 4, of which they are the constants on the page.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1159, Section A.3, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.IncumbentLowerBound

/-- Proof of Theorem 3, first display on p. 1159: because `β ∈ [b_min, b_max]`,
`Δ^π(T) = sup_{β∈𝔅, ψ(β)≠0} {−β Σ_{t=1}^T E^π_β(x_t − ψ(β))²}
  ≥ |b_max| sup_{β∈𝔅, ψ(β)≠0} Σ_{t=2}^T c₀ / (c₁ + (u − l)²(t − 1))`,
with `c₀, c₁` the constants of Lemma 4 (the summand does not depend on `β`, so the second
supremum is the sum itself). Lean period `t` is the paper's period `t + 1`: the paper's
`Σ_{t=1}^T` is `Finset.range T`, and the paper's `Σ_{t=2}^T` with `t − 1` is `Finset.Ico 1 T`
with the Lean index `t`. The constants depend only on the model `M`. -/
theorem regret_eq_neg_beta_sum_sqErr (M : Model) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        worstRegret M P ε π T
            = ⨆ β : M.Bexcl, -(β : ℝ) * ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t ∧
          |M.bMax| * ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + (M.u - M.l) ^ 2 * (t : ℝ))
            ≤ worstRegret M P ε π T := by sorry

end KeskinZeevi.IncumbentLowerBound
