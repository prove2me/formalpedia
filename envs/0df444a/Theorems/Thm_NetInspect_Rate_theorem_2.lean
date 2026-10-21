-- Prove2me | Theorems.Thm_NetInspect_Rate_theorem_2
-- name    : NetInspect.Rate.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:34.307454+00:00
-- url     : https://prove2.me/theorems/2c212a8b-c3df-4cd8-8a63-4c899a3f4363
-- title:
--   Theorem 2, p. 17 — the equilibrium detection rate r*_{b1} is the same in every Γ(b1,b2) with 1 ≤ b2 < m*, and Γ(b1,1) equilibrium inspection strategies stay equilibrium strategies
-- statement:
--   Let $\mathcal G=(\mathcal V,\mathcal E,\{\mathcal C_i\})$ be a detection model and $b_1\in\mathbb N$ the number of detectors. Then:
--
--   1. there is a number $r^*_{b_1}\in[0,1]$ such that, for every $b_2$ with $1\le b_2<m^*$ and every Nash equilibrium $\sigma^*$ of $\Gamma(b_1,b_2)$,
--   $$
--   r(\sigma^*)=r^*_{b_1};
--   $$
--   2. every inspection strategy $\sigma^{1*}$ that is part of a Nash equilibrium of $\Gamma(b_1,1)$ is also part of a Nash equilibrium of every game $\Gamma(b_1,b_2)$ with $1\le b_2<m^*$: some attack strategy $\sigma^{2\prime}\in\Delta(\mathcal A_2)$ makes $(\sigma^{1*},\sigma^{2\prime})$ an equilibrium of $\Gamma(b_1,b_2)$.
--
--   The expected detection rate in equilibrium depends on the defender's resources only, as long as the attacker's resources stay below the maximum set packing size $m^*$; and the defender can compute an equilibrium inspection strategy as if the attacker had a single resource.
--
--   **Formalization Note** The number $r^*_{b_1}$ is chosen after $b_1$ and before $b_2$, as in (17). The hypothesis $b_2\ge 1$ is added: in $\Gamma(b_1,0)$ every profile is an equilibrium and the rate is $1$, whereas $r^*_{b_1}<1$ for $b_1<n^*$; the paper's base case is $\Gamma(b_1,1)$. The case $b_1\ge n^*$ is included, as printed; it relies on the convention $F(S,\emptyset)/|\emptyset|=1$ of the rate. If $m^*\le 1$ there is no admissible $b_2$ and both parts hold vacuously. The new attack strategy in part 2 lives on the action set of $\Gamma(b_1,b_2)$ and is not required to be related to the equilibrium attack strategy of $\Gamma(b_1,1)$.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. 17, Theorem 2, (17)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Theorem 2 (p. 17), (17): for every `b1` there is `r*_{b1} ∈ [0, 1]` equal to the expected
detection rate of every equilibrium of every game `Γ(b1, b2)` with `1 ≤ b2 < m*`; and every
equilibrium inspection strategy of `Γ(b1, 1)` is an equilibrium inspection strategy of every
`Γ(b1, b2)` with `1 ≤ b2 < m*`. -/
theorem theorem_2 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) (b1 : ℕ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2') := by sorry

end NetInspect.Rate
