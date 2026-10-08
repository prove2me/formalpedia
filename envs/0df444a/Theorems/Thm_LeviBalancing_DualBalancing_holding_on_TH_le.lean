-- Prove2me | Theorems.Thm_LeviBalancing_DualBalancing_holding_on_TH_le
-- name    : LeviBalancing.DualBalancing.holding_on_TH_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:24:15.648956+00:00
-- url     : https://prove2.me/theorems/b476bce4-c1d6-4599-80a8-6d3154e1c926
-- title:
--   Lemma 4.2, p. 294 — $\sum_{t\in\mathcal T_H} H_t^B \le H^{P}$ on every realization
-- statement:
--   Fix an instance, a realization of the demands $d_1, \dots, d_T \ge 0$, and two order sequences $Q^B, Q^P$ with nonnegative orders in periods $1, \dots, T$. Let $Y^B_t$ and $Y^P_t$ be the resulting inventory positions after ordering, and let
--   $$\mathcal T_H = \{\, t \in \{1, \dots, T-L\} : Y^B_t < Y^P_t \,\}$$
--   be the periods in which $P$ holds more inventory than $B$. Then the marginal holding cost of $B$ over these periods is at most the total marginal holding cost of $P$:
--   $$\sum_{t \in \mathcal T_H} H^B_t \;\le\; H^P := \sum_{t=1}^{T-L} H^P_t .$$
--
--   Together with Lemma 4.3 this gives the pathwise bound $\sum_{t\in\mathcal T_H} H^B_t + \sum_{t \in \mathcal T_\Pi} \Pi^B_t \le \mathcal C(P)$ from which Theorem 4.1 follows.
--
--   **Formalization Note** The paper states this for the dual-balancing policy $B$ and an optimal policy, "with probability one". The proof uses neither the balancing rule nor optimality, only that both order processes are nonnegative on the same demand path, so it is stated for every realization and every pair of nonnegative order sequences; this is a strengthening of the page's statement. $H^{OPT}$ is read as the marginal total $\sum_{t=1}^{T-L} H^P_t$ of Eq. (4), which is at most the physical holding cost of $P$ (Eq. (3)), so this reading is also the stronger one.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 294 (PDF p. 11), Lemma 4.2

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open Finset

namespace LeviBalancing.DualBalancing

/-- Lemma 4.2, p. 294 (pathwise): for every demand realization and any two order processes with
nonnegative orders (`B` and a comparison policy `P`), the marginal holding cost of `B` over the
periods `𝒯_H = {t : Y_t^B < Y_t^P}` is at most the total marginal holding cost
`H^P = ∑_{t=1}^{T−L} H_t^P` of `P`. -/
theorem holding_on_TH_le (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qB t < invPositionAfter I d qP t),
        marginalHolding I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalHolding I d qP t := by sorry

end LeviBalancing.DualBalancing
