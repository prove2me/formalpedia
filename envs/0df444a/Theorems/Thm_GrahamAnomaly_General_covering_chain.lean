-- Prove2me | Theorems.Thm_GrahamAnomaly_General_covering_chain
-- name    : GrahamAnomaly.General.covering_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:03:49.237982+00:00
-- url     : https://prove2.me/theorems/c4bef91e-2ded-4bfa-8f25-7e4827c26ff9
-- title:
--   (1), proof of Theorem 1, p. 420 — a precedence chain covers idle times
-- statement:
--   Let $r\ge1$ tasks with positive durations $\mu'(T_j)$ be scheduled by Graham's list rule on $n'\ge1$ identical processors under a strict precedence order $\prec'$ and any priority list. Write $S'_j$ for their start times and $\omega'$ for the finishing time. There is a finite chain $C=(T_{j_m},\ldots,T_{j_1})$ in increasing $\prec'$ order, containing a task that finishes at $\omega'$, such that
--
--   $$\forall t\in[0,\omega'),\quad \bigl(\text{some processor is idle at }t\bigr)\Longrightarrow\bigl(\text{some task of }C\text{ runs at }t\bigr).$$
--
--   This chain is the link between idle processor time in the second run and a path of precedence-constrained work.
--
--   **Formalization Note** The paper's set $B$ excludes times when every processor is idle. Under the list rule, all processors cannot be idle before the last task finishes, so the formula uses failure of “all processors busy” to describe $B$. Running intervals are half-open.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), pp. 419–420, display (1) and following sentence in proof of Theorem 1; https://doi.org/10.1137/0117039

import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Display (1) in the proof of Theorem 1: a precedence chain ending at a
last-finishing task covers each time when a processor is idle. -/
theorem covering_chain {r n' : ℕ} (hr : 0 < r) (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (L' : Fin r ≃ Fin r) (G' : Schedule n' μ' prec')
    (hG' : IsListSchedule L' G') :
    ∃ c : List (Fin r), c.Chain' prec' ∧
      (∃ j ∈ c, G'.S j + μ' j = G'.finish) ∧
      ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
        ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a := by sorry

end GrahamAnomaly.General
