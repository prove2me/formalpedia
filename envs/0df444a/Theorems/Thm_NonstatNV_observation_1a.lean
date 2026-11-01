-- Prove2me | Theorems.Thm_NonstatNV_observation_1a
-- name    : NonstatNV.observation_1a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:10.463926+00:00
-- url     : https://prove2.me/theorems/cdb679af-3b9a-4864-b9c4-cb30dd1be3f4
-- title:
--   Observation 1a) — the Prediction Policy has regret at most $2\ell T^a$
-- statement:
--   Consider a model satisfying the standing assumptions and Assumption 2 with constant $\ell$, and an argmin selection. Fix $v\in[0,1]$ and $\alpha\in[0,1]$. For every horizon $T$, every instance $(\mu_t,b_t,h_t)_{t\le T}$ with demand variation $V_\mu\le T^v$, and every prediction sequence $(a_t)$ with total error
--
--   $$
--   \sum_{t=1}^{T}|a_t-\mu_t|\le T^{\alpha},
--   $$
--
--   the regret of the Prediction Policy satisfies
--
--   $$
--   \mathbb E\Big[\sum_{t=1}^{T}\big(C_t(\mu_t,q_t)-C_t(\mu_t,q_t^*)\big)\Big]\le 2\ell\,T^{\alpha}.
--   $$
--
--   The Prediction Policy translates prediction error directly into regret, without knowing $\alpha$; this is the "$a$" branch of the main result.
--
--   Differences from the source:
--   - encoding: worst-case regret R(T) = sup over D(v) and predictions with error ≤ T^a, bounded by C T^a with C ≤ 2ℓ → the regret of every instance of the class is at most 2ℓ T^α; reason: a bound for every instance is equivalent to a bound on the supremum, and C ≤ 2ℓ is equivalent to C = 2ℓ
--   - encoding: a is the smallest exponent with prediction error ≤ T^a → any α ∈ [0, 1] with prediction error ≤ T^α; reason: the bound 2ℓT^α increases with α for T ≥ 1, so the two forms are equivalent (for T = 0 both sides are 0)
--   - encoding: q_t ← argmin_{q∈Q} C_t(μ̂_t, q) → q_t = sel(μ̂_t, b_t, h_t) for an arbitrary measurable argmin selection sel; reason: ties are broken by an arbitrary selection; the statement holds for every selection
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Observation 1 a), p.21 (proof p.34)

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost
import Definitions.Def_NonstatNV_Model_IsArgminSelection
import Definitions.Def_NonstatNV_Model_IsInstance
import Definitions.Def_NonstatNV_demandVariation
import Definitions.Def_NonstatNV_Model_intervalRegret
import Definitions.Def_NonstatNV_Model_predictionPolicy

open MeasureTheory

namespace NonstatNV

/-- **Observation 1 a)** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.21; proof p.34). Fix any variation parameter `v ∈ [0, 1]` and
any accuracy parameter `a ∈ [0, 1]`. The Prediction Policy achieves worst-case regret
`R^{π^prediction}(T) ≤ C T^a` with `C ≤ 2ℓ`: for every horizon `T`, every instance in `𝒟(v)`
(`V_μ ≤ T^v`) whose predictions have total error `Σ_{t=1}^T |a_t − μ_t| ≤ T^α`, the regret is at most
`2ℓ T^α`.

**Formalization Note** The accuracy exponent is named `α` (the predictions are the sequence `a`).
The bound is stated with `C = 2ℓ`, which is equivalent to `C ≤ 2ℓ`. The argmin is taken by an
arbitrary measurable selection `sel`; the worst-case regret is stated as a bound for every instance. -/
theorem observation_1a (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (sel : ℝ → ℝ → ℝ → ℝ) (hsel : M.IsArgminSelection sel)
    (T : ℕ) (v α : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (μ b h a : ℕ → ℝ) (hinst : M.IsInstance T μ b h)
    (hV : demandVariation μ T ≤ (T : ℝ) ^ v)
    (hpred : ∑ t ∈ Finset.Icc 1 T, |a t - μ t| ≤ (T : ℝ) ^ α) :
    M.intervalRegret μ b h (M.predictionPolicy sel b h a) 1 T ≤ 2 * ℓ * (T : ℝ) ^ α := by sorry

end NonstatNV
