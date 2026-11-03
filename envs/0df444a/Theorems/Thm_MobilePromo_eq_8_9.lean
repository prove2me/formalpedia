-- Prove2me | Theorems.Thm_MobilePromo_eq_8_9
-- name    : MobilePromo.eq_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:09.965292+00:00
-- url     : https://prove2.me/theorems/71916342-db4d-4994-b646-a9f347f7a0e1
-- title:
--   (8) and (9): the regret of BidAlloc over $S_0$ cycles
-- statement:
--   Let Assumptions 1, 2 and 3 hold, and let $S_0=\lceil\sqrt{2IT/L}\rceil$. There are constants $K_0>0$, $K_1>1$, $K_{mle}>0$, independent of $I$ and $T$, such that for BidAlloc $\hat\pi$,
--
--   $$
--   \mathrm{Regret}(\hat\pi,I;\gamma^{(0)})\le K_0\sum_{s=1}^{S_0}\bigl(\text{first expectation of (8) in cycle }s+\text{second expectation of (8) in cycle }s\bigr)
--   $$
--
--   and
--
--   $$
--   \mathrm{Regret}(\hat\pi,I;\gamma^{(0)})\le K_0S_0(\hat K+\check K),\qquad\hat K=(b^{\max}-b^{\min})^2\sum_l\frac{k_l}{q_l},\quad\check K=K_1^{2T}LK_{mle}.
--   $$
--
--   The $S_0$ cycles cover the horizon, which gives the order $\sqrt{IT}$.
--
--   Differences from the source:
--   - reading: (8) is printed as a chain ending in equalities → the bound $\le$ of the regret by the sum over cycles $s\le S_0$; reason: the chain starts from the inequality of Lemma 2, and the sum is over the cycles that meet the horizon
--   - reading: the display of Regret on p.15 and the objective (P) write $\mathbb E\sum(b^\pi_{i,t,l}-e)q_ld_{i,t}$ → the display of p.16: `expCost` is the expectation of the realized cost $\sum(b-e)\mathbb 1\{\zeta_{i,t}=l\}d_{i,t}$; reason: with $d_{i,t}$ the realized win the p.15 display counts $q_l$ twice, and for $L=T=1$, $q<1$ a clairvoyant policy would have regret $(e-b^*)qp(1-q)>0$ per season; the proof uses the p.16 form
--   - encoding: the expectation over random histories → a finite sum over outcome paths `ω : Fin (I * T) → Outcome L` weighted by `pathProb`, seasons 0-based; reason: a period has finitely many outcomes; no instance changes
--   - encoding: "there exist $k_l\in\mathbb N$ and a vector of exploration bids" (Assumption 2, p.12), the input of the policy (p.17) → the bids are the parameter `X : Exploration M`, with $k_l\ge 1$; reason: $\bar b_l$ is an input on p.17, and the phase needs a bid to place
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, (8), p.19; (9), p.19; $S_0$, p.18

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption2
import Definitions.Def_MobilePromo_Assumption3
import Definitions.Def_MobilePromo_phaseGap

set_option autoImplicit false

namespace MobilePromo

/-- The decomposition (8) and the bound (9) (SSRN 3523491, (8), p.19, and (9), p.19, with
`S₀ = ⌈√(2IT/L)⌉`, p.18): the regret of `BidAlloc` is at most `K₀ ∑_{s=1}^{S₀}` of the two expectations of (8)
of cycle `s`, and hence at most `K₀ S₀ (K̂ + Ǩ)`, where `K̂ = (bmax - bmin)² ∑_l k_l / q_l` and
`Ǩ = (K₁)^{2T} L K_mle`.

**Formalization Note** Each active period of the horizon lies in exactly one phase of a cycle `≤ S₀`,
because the first `S₀` cycles hold at least `I T` bids. -/
theorem eq_8_9 (M : Model) (h1 : Assumption1 M) (X : Exploration M) (h2 : Assumption2 M X) :
    ∃ K₀ K₁ Kmle : ℝ, 0 < K₀ ∧ 1 < K₁ ∧ 0 < Kmle ∧
      ∀ (mle : MLESelector M X) {T : ℕ} (S : Schedule T) (I : ℕ), Assumption3 M S I →
        ∀ γ₀ ∈ M.Gamma0,
          let S₀ : ℕ := ⌈√(2 * (I : ℝ) * T / M.L)⌉₊
          regret M S (bidAlloc M X mle S) γ₀ I ≤
              K₀ * ∑ s ∈ Finset.Icc 1 S₀,
                (phaseGap M X mle S γ₀ I s true + phaseGap M X mle S γ₀ I s false) ∧
            regret M S (bidAlloc M X mle S) γ₀ I ≤
              K₀ * S₀ * ((M.bmax - M.bmin) ^ 2 * (∑ l, (X.k l : ℝ) / M.q l) +
                K₁ ^ (2 * T) * M.L * Kmle) := by sorry

end MobilePromo
