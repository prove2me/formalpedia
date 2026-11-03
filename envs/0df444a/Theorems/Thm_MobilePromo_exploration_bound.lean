-- Prove2me | Theorems.Thm_MobilePromo_exploration_bound
-- name    : MobilePromo.exploration_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:39.156741+00:00
-- url     : https://prove2.me/theorems/254424c2-b743-4120-a89b-b589f201e491
-- title:
--   p.19: each exploration phase contributes at most $\hat K$
-- statement:
--   Let Assumption 1 hold and $\gamma^{(0)}\in\Gamma^{(0)}$. For every cycle $s\ge1$, every horizon and every schedule, the first expectation of (8) satisfies
--
--   $$
--   \mathbb E\Bigl[\sum_{i=1}^I\sum_{t=1}^T\sum_l\mathbb 1\{\zeta_{i,t}=l\}\mathbb 1\{(i,t)\in\mathcal A_{s_1}(X^{\hat\pi})\}\bigl(b^{\hat\pi}_{i,t,l}-b^*_{i,t,l}\bigr)^2\Bigr]\le(b^{\max}-b^{\min})^2\sum_l\frac{k_l}{q_l}=\hat K .
--   $$
--
--   So the cost of exploration in one cycle does not grow with $s$, $I$ or $T$.
--
--   Differences from the source:
--   - generalization: the proof of Theorem 1, under Assumptions 1, 2, 3 → only Assumption 1, for every horizon, schedule and likelihood selector; reason: the bound uses only that both bids lie in $B$; it specializes to the printed setting
--   - encoding: the expectation over random histories → a finite sum over outcome paths `ω : Fin (I * T) → Outcome L` weighted by `pathProb`, seasons 0-based; reason: a period has finitely many outcomes; no instance changes
--   - encoding: "there exist $k_l\in\mathbb N$ and a vector of exploration bids" (Assumption 2, p.12), the input of the policy (p.17) → the bids are the parameter `X : Exploration M`, with $k_l\ge 1$; reason: $\bar b_l$ is an input on p.17, and the phase needs a bid to place
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, p.19, first expectation of (8)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_phaseGap

set_option autoImplicit false

namespace MobilePromo

/-- The exploration phases (SSRN 3523491, p.19): for every cycle `s ≥ 1`, the first expectation of (8) is at
most `K̂ = (bmax - bmin)² ∑_l k_l / q_l`. -/
theorem exploration_bound (M : Model) (h1 : Assumption1 M) (X : Exploration M)
    (mle : MLESelector M X) {T : ℕ} (S : Schedule T) (I s : ℕ) (hs : 1 ≤ s) (γ₀ : M.ParamVec)
    (hγ₀ : γ₀ ∈ M.Gamma0) :
    phaseGap M X mle S γ₀ I s true ≤ (M.bmax - M.bmin) ^ 2 * ∑ l, (X.k l : ℝ) / M.q l := by sorry

end MobilePromo
