-- Prove2me | Theorems.Thm_NonstatNV_observation_2
-- name    : NonstatNV.observation_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:11.990015+00:00
-- url     : https://prove2.me/theorems/cede6a47-8e4a-42e7-9814-3655f5933e85
-- title:
--   Observation 2 — any policy has $\mathcal R^\pi(T)[a,b]\le C(b-a+1)$
-- statement:
--   Consider a model satisfying the standing assumptions and Assumption 2. There is a constant $C\in(0,\infty)$, depending only on the model, such that for every horizon $T$, every policy $\pi$ (orders in $Q$, measurable, depending only on past demands), every instance $(\mu_t,b_t,h_t)$ and every pair of periods $1\le a\le b\le T$,
--
--   $$
--   \mathbb E\Big[\sum_{t=a}^{b}\big(C_t(\mu_t,q_t)-C_t(\mu_t,q_t^*)\big)\Big]\le C\,(b-a+1).
--   $$
--
--   The regret per period is uniformly bounded, so stretches of time where nothing better is known cost at most linearly.
--
--   Differences from the source:
--   - reading: time periods a, b → 1 ≤ a ≤ b ≤ T; reason: R[a, b] is the regret over the periods from a to b; for a > b + 1 the printed right side C(b − a + 1) is negative and the statement would be false
--   - encoding: sup over D ∈ D(v) → a bound for every instance with means in [μmin, μmax] and costs in their boxes; reason: the bound does not involve v; a bound for every instance is equivalent to a bound on the supremum over D(v) for every v
--   - generalization: for any policy, with q*_t ∈ argmin (minimizers presupposed) → no existence of minimizers assumed; the clairvoyant cost is the infimum over Q; reason: when minimizers exist the infimum is the minimum, so the statement specializes to the source's
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Observation 2 and the definition of $\mathcal R^\pi(T)[a,b]$, p.34

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_Model_IsPolicy
import Definitions.Def_NonstatNV_Model_intervalRegret

open MeasureTheory

namespace NonstatNV

/-- **Observation 2** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.34). For any policy `π`, `R^π(T)[a, b] ≤ C(b − a + 1)` for some
universal constant `C ∈ (0, ∞)`: there is `C > 0`, depending only on the model, such that for every
horizon `T`, every policy, every instance and every pair of periods `1 ≤ lo ≤ hi ≤ T`, the regret
from period `lo` to period `hi` is at most `C (hi − lo + 1)`.

**Formalization Note** The periods `a, b` of the page are `lo ≤ hi`. `C` is chosen before the
horizon, the policy and the instance. -/
theorem observation_2 (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ) (q : ℕ → (ℕ → ℝ) → ℝ), M.IsPolicy T q →
      ∀ μ b h : ℕ → ℝ, M.IsInstance T μ b h →
      ∀ lo hi : ℕ, 1 ≤ lo → lo ≤ hi → hi ≤ T →
        M.intervalRegret μ b h q lo hi ≤ C * ((hi : ℝ) - lo + 1) := by sorry

end NonstatNV
