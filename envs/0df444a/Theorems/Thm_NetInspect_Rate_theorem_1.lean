-- Prove2me | Theorems.Thm_NetInspect_Rate_theorem_1
-- name    : NetInspect.Rate.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:21.215109+00:00
-- url     : https://prove2.me/theorems/46d6a02e-fd8e-4a2f-a26d-ed41757f588b
-- title:
--   Theorem 1, pp. 13–14 — for b1 < n*, b2 < m*, equilibria use exactly b1 detectors and b2 attacks, and are the solutions of (LP̄1), (LP̄2)
-- statement:
--   Let $\mathcal G$ be a detection model, $b_1<n^*$ and $1\le b_2<m^*$. Then:
--
--   1. in every Nash equilibrium $(\sigma^{1*},\sigma^{2*})$ of $\Gamma(b_1,b_2)$,
--   $$
--   |S|=b_1\ \text{ for all } S\in\operatorname{supp}(\sigma^{1*}),\qquad |T|=b_2\ \text{ for all } T\in\operatorname{supp}(\sigma^{2*})\qquad\text{(10), (11)};
--   $$
--   2. an inspection strategy $\sigma^1\in\Delta(\mathcal A_1)$ is an equilibrium strategy (some $\sigma^2$ makes $(\sigma^1,\sigma^2)$ an equilibrium) if and only if it vanishes outside $\bar{\mathcal A}_1=\{S:|S|=b_1\}$ and its restriction to $\bar{\mathcal A}_1$ is an optimal solution of
--   $$
--   (\overline{\mathrm{LP}}_1)\qquad \min_{\sigma^1\in\Delta(\bar{\mathcal A}_1)}\ \max_{T\in\bar{\mathcal A}_2}U(\sigma^1,T);
--   $$
--   3. an attack strategy $\sigma^2\in\Delta(\mathcal A_2)$ is an equilibrium strategy if and only if it vanishes outside $\bar{\mathcal A}_2=\{T:|T|=b_2\}$ and its restriction to $\bar{\mathcal A}_2$ is an optimal solution of
--   $$
--   (\overline{\mathrm{LP}}_2)\qquad \max_{\sigma^2\in\Delta(\bar{\mathcal A}_2)}\ \min_{S\in\bar{\mathcal A}_1}U(S,\sigma^2).
--   $$
--
--   Both players must use all their resources in equilibrium, and the equilibria can be computed from linear programs over the smaller action sets $\bar{\mathcal A}_1,\bar{\mathcal A}_2$.
--
--   **Formalization Note** "The NE of $\Gamma$ can be obtained by solving $(\overline{\mathrm{LP}}_1)$ and $(\overline{\mathrm{LP}}_2)$" is read as parts 2 and 3: the equilibrium strategies of each player are exactly the extensions by zero of the optimal solutions of the corresponding barred program. $b_1<n^*$ and $b_2<m^*$ are the hypotheses of the theorem; $b_2\ge 1$ is added (with $b_2=0$ every profile is an equilibrium and (10) fails).
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, pp. 13–14, Theorem 1, (10)–(11), (LP̄1)–(LP̄2)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Theorem 1 (pp. 13–14): if `b1 < n*` and `1 ≤ b2 < m*`, every equilibrium of `Γ(b1, b2)`
randomizes over positionings of size exactly `b1` (10) and attack plans of size exactly `b2`
(11); and the equilibrium strategies of each player are exactly the strategies supported on
`Ā1` (resp. `Ā2`) whose restriction is an optimal solution of (LP̄1) (resp. (LP̄2)). -/
theorem theorem_1 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 →
      (∀ S : Act V b1, 0 < σ1 S → S.1.card = b1) ∧
      (∀ T : Act E b2, 0 < σ2 T → T.1.card = b2)) ∧
    (∀ σ1 : Act V b1 → ℝ, (∃ σ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ S : Act V b1, S.1.card ≠ b1 → σ1 S = 0) ∧ G.IsOptLP1bar b1 b2 (restrictEx σ1))) ∧
    (∀ σ2 : Act E b2 → ℝ, (∃ σ1 : Act V b1 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ T : Act E b2, T.1.card ≠ b2 → σ2 T = 0) ∧ G.IsOptLP2bar b1 b2 (restrictEx σ2))) := by sorry

end NetInspect.Rate
