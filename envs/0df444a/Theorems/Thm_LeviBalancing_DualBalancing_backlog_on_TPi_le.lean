-- Prove2me | Theorems.Thm_LeviBalancing_DualBalancing_backlog_on_TPi_le
-- name    : LeviBalancing.DualBalancing.backlog_on_TPi_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:24:06.131033+00:00
-- url     : https://prove2.me/theorems/6835c594-7b87-4750-bb24-d70fb43bb9f6
-- title:
--   Lemma 4.3, p. 294 — $\sum_{t\in\mathcal T_\Pi} \Pi_t^B \le \Pi^{P}$ on every realization
-- statement:
--   Fix an instance, a realization of the demands $d_1, \dots, d_T \ge 0$, and two order sequences $Q^B, Q^P$ with nonnegative orders in periods $1, \dots, T$. Let $Y^B_t$ and $Y^P_t$ be the resulting inventory positions after ordering, and let
--   $$\mathcal T_\Pi = \{\, t \in \{1, \dots, T-L\} : Y^B_t \ge Y^P_t \,\}$$
--   be the periods in which $B$ holds at least as much inventory as $P$. Then the marginal backlogging cost of $B$ over these periods is at most the total marginal backlogging cost of $P$:
--   $$\sum_{t \in \mathcal T_\Pi} \Pi^B_t \;\le\; \Pi^P := \sum_{t=1}^{T-L} \Pi^P_t .$$
--
--   This is the backlogging half of the pathwise comparison behind Theorem 4.1.
--
--   **Formalization Note** As for Lemma 4.2, the statement holds for every realization and every pair of nonnegative order sequences, which strengthens the page's "for the dual-balancing policy and OPT, with probability one". $\Pi^{OPT}$ is read as the marginal total $\sum_{t=1}^{T-L}\Pi^P_t$ of Eq. (4).
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 294 (PDF p. 11), Lemma 4.3

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open Finset

namespace LeviBalancing.DualBalancing

/-- Lemma 4.3, p. 294 (pathwise): for every demand realization and any two order processes with
nonnegative orders, the marginal backlogging cost of `B` over the periods
`𝒯_Π = {t : Y_t^B ≥ Y_t^P}` is at most the total marginal backlogging cost
`Π^P = ∑_{t=1}^{T−L} Π_t^P` of `P`. -/
theorem backlog_on_TPi_le (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalBacklog I d qP t := by sorry

end LeviBalancing.DualBalancing
