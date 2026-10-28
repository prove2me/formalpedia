-- Prove2me | Theorems.Thm_NetInspect_Rate_theorem_2_step_ia
-- name    : NetInspect.Rate.theorem_2_step_ia
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:22.329138+00:00
-- url     : https://prove2.me/theorems/de615f2e-3072-4661-b257-d0897286ac0c
-- title:
--   Proof of Theorem 2, step (i.a), pp. ec11–ec13 — for b2 = 1, some optimal solution of (LP̄2) targets every component with probability ≤ 1/m*
-- statement:
--   Let $\mathcal G$ be a detection model, $b_1<n^*$, and suppose $1<m^*$ (the standing assumption $b_2<m^*$ for $b_2=1$). Then there is an optimal solution $\sigma^{2*}\in\Delta(\bar{\mathcal A}_2)$ of
--   $$
--   (\overline{\mathrm{LP}}_2)\qquad\max_{\sigma^2\in\Delta(\bar{\mathcal A}_2)}\ \min_{S\in\bar{\mathcal A}_1}U(S,\sigma^2),\qquad \bar{\mathcal A}_2=\{T:|T|=1\},
--   $$
--   such that
--   $$
--   \rho_{\sigma^{2*}}(e)\le\frac{1}{m^*}\qquad\text{for all } e\in\mathcal E.
--   $$
--
--   With a single attack resource, the attacker has an optimal strategy that spreads its attack: no component is targeted with probability above $1/m^*$. Through Lemma EC.4 this strategy scales to every $b_2<m^*$, which is how the proof of Theorem 2 relates $\Gamma(b_1,b_2)$ to $\Gamma(b_1,1)$.
--
--   **Formalization Note** The claim is stated for every $b_1<n^*$, as printed. The paper's argument picks a node of an optimal positioning and divides by $b_1-1$, so it covers $b_1\ge 2$ only; the statement itself is not changed.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, pp. ec11–ec13, proof of Theorem 2, step (i.a)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Proof of Theorem 2, step (i.a) (pp. ec11–ec13): for `b1 < n*` and `b2 = 1 < m*`, some
optimal solution `σ2*` of (LP̄2) attacks every component with probability at most `1/m*`. -/
theorem theorem_2_step_ia {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 : ℕ} (hb1 : b1 < G.nStar) (hm : 1 < G.mStar) :
    ∃ σ2 : ActEx E 1 → ℝ, G.IsOptLP2bar b1 1 σ2 ∧
      ∀ e : E, marg σ2 e ≤ 1 / (G.mStar : ℝ) := by sorry

end NetInspect.Rate
