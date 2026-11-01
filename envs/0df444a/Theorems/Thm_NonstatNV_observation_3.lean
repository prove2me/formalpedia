-- Prove2me | Theorems.Thm_NonstatNV_observation_3
-- name    : NonstatNV.observation_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:29.400796+00:00
-- url     : https://prove2.me/theorems/a2358839-ec4a-4df2-b0e2-d31d8c4b7ddd
-- title:
--   Observation 3 — a plug-in policy has regret at most $2\ell\,\mathbb E\sum_t|\hat\mu_t-\mu_t|$
-- statement:
--   Consider a model satisfying the standing assumptions and Assumption 2 with constant $\ell$. Let $\pi$ be a policy for horizon $T$ and $(\mu_t,b_t,h_t)$ an instance, and let $1\le a$ and $b\le T$. Suppose that for every period $a\le t\le b$ the policy first forms a measurable estimate $\hat\mu_t\in[\mu_{\min},\mu_{\max}]$ of the mean and then orders $q_t\in\arg\min_{q\in Q}C_t(\hat\mu_t,q)$. Then
--
--   $$
--   \mathbb E\Big[\sum_{t=a}^{b}\big(C_t(\mu_t,q_t)-C_t(\mu_t,q_t^*)\big)\Big]\le 2\ell\;\mathbb E\Big[\sum_{t=a}^{b}|\hat\mu_t-\mu_t|\Big].
--   $$
--
--   Taking suprema over the instance class gives the printed form $\mathcal R^\pi(T)[a,b]\le C\sup_{D\in\mathcal D(v)}\mathbb E\{\sum_{t=a}^b|\hat\mu_t-\mu_t|\}$ with $C=2\ell$: a policy that estimates the mean accurately has low regret.
--
--   Differences from the source:
--   - generalization: R[a, b] ≤ C · sup_{D∈D(v)} E Σ|μ̂_t − μ_t| for some universal constant C → for each instance, its regret over [a, b] ≤ 2ℓ · E Σ|μ̂_t − μ_t| on the same instance; reason: taking suprema over D(v) on both sides gives the printed bound with C = 2ℓ, the constant of the paper's proof
--   - generalization: μ̂_t is the policy's estimate (computed from past demands) → μ̂_t is any measurable function of the demand path with values in [μmin, μmax]; reason: the bound holds for any such estimate; the policy's estimates are a special case
--   - generalization: q*_t ∈ argmin (minimizers presupposed) → no existence of minimizers at the true means assumed; the clairvoyant cost is the infimum over Q; reason: when minimizers exist the infimum is the minimum
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Observation 3, p.35 (proof p.35)

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_Model_IsPolicy
import Definitions.Def_NonstatNV_Model_intervalRegret

open MeasureTheory

namespace NonstatNV

/-- **Observation 3** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.35). For any policy `π` that, from period `lo` to period `hi`,
first estimates the mean at time `t` to be `μ̂_t ∈ [μmin, μmax]` and then orders
`q_t ∈ argmin_{q∈Q} C_t(μ̂_t, q)`,
`R^π(T)[lo, hi] ≤ C · E[Σ_{t=lo}^{hi} |μ̂_t − μ_t|]` with `C = 2ℓ` (the constant of the proof).

**Formalization Note** The bound is stated per instance; taking suprema over the instance class gives
the printed form. The estimate `μhat t ω` (the `μ̂_t` of the page) is any measurable function of the demand path with values in
`[μmin, μmax]`. -/
theorem observation_3 (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (T : ℕ) (q : ℕ → (ℕ → ℝ) → ℝ) (hq : M.IsPolicy T q) (μhat : ℕ → (ℕ → ℝ) → ℝ)
    (μ b h : ℕ → ℝ) (hinst : M.IsInstance T μ b h) (lo hi : ℕ) (hlo : 1 ≤ lo) (hhi : hi ≤ T)
    (hμhat : ∀ t ∈ Finset.Icc lo hi, Measurable (μhat t) ∧ ∀ ω, μhat t ω ∈ Set.Icc M.μmin M.μmax ∧
      ∀ q' ∈ M.Q, M.cost (μhat t ω) (b t) (h t) (q t ω) ≤ M.cost (μhat t ω) (b t) (h t) q') :
    M.intervalRegret μ b h q lo hi ≤
      2 * ℓ * ∫ ω, (∑ t ∈ Finset.Icc lo hi, |μhat t ω - μ t|) ∂(M.demandLaw μ) := by sorry

end NonstatNV
