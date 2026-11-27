-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_3
-- name    : IncentiveFinNet.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:32:37.516845+00:00
-- url     : https://prove2.me/theorems/122bc9ea-49f1-4bf9-b987-2b8154adee38
-- title:
--   Theorem 3 — every stable point is Higher-Order Nash Stable (corrected: the cartel is nonempty)
-- statement:
--   Every stable point $(W,P)$ of a network setting (Definition 3) is Higher-Order Nash Stable. That is:
--
--   1. **Nash equilibrium.** For every agent $i$, every action $(w'_j,p'_j)_{j\in J_i}$ and every resulting network $(W',P')$ (Definition 4),
--   $$
--   g_i(W',P')\le g_i(W,P).
--   $$
--   Here a proposal is accepted exactly when it strictly raises the counterparty's utility, and a rejected contract may be kept or cancelled.
--   2. **Cartel robustness.** For every nonempty proper subset $T\subsetneq[n]$ and every feasible $(W',P')$ that differs from $(W,P)$ only at entries $(a,b)$ with $a,b\in T$, some agent $k\in T$ has $g_k(W',P')\le g_k(W,P)$.
--
--   No single agent can profitably renegotiate its contracts, and no proper coalition can rearrange the contracts among its members so that all of them gain.
--
--   Differences from the source:
--
--   - correction: cartel robustness for any proper subset S ⊂ [n] → for every nonempty proper subset T; reason: at S = ∅ the printed clause fails for every (W,P): (W,P) itself is feasible, differs from (W,P) only on ∅, and all agents of ∅ gain vacuously, so Theorem 3 as printed is false for every stable point; the proof (A.6, p.37) takes (W′,P′) ≠ (W,P), which forces S ≠ ∅, and for nonempty S the two conditions agree. Excluded case: only S = ∅
--   - generalization: Definition 4, rule 2: i cancels a rejected contract iff this strictly increases i's utility → every keep-or-cancel choice for each rejected contract, and for the self-investment W′_ii any of the proposed value, the old value or 0; reason: the Nash clause then covers more resulting networks; the network produced by the paper's rule is one of them, so the Lean statement specializes to the printed one
--   - reading: "the new (w′_ij, p′_ij) raises j's utility" → g_j(W,P) < g_j at the network in which only the contract between i and j is replaced; reason: j's utility depends only on column j, which in the resulting network differs from (W,P) only at (i,j); "raises" read as strict, as in Definition 5's "strictly better"
--   - encoding: an action (w′_ij, p′_ij)_{j∈J_i} → two functions w′, p′ : Fin n → ℝ of which only the values on J_i are used; reason: Lean convention; same actions
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 3, p.13; Definitions 4–5, pp.12–13; restated and proved in A.6, p.37

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_ResultingNetwork
import Definitions.Def_IncentiveFinNet_Supplement_HigherOrderNashStable

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 3 (Higher-Order Nash Stability)**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3,
p.13 (restated in A.6, p.37): "Any stable point `(W, P)` is Higher-Order Nash Stable."

Stated for every network setting and every stable point (Definition 3). Higher-Order Nash
Stability is `HigherOrderNashStable` (Definition 5, p.13) with the resulting networks of
`ResultingNetwork` (Definition 4, pp.12–13).

**Formalization Note** The cartel clause ranges over nonempty proper subsets; the printed clause
fails at the empty cartel for every `(W, P)` (see `HigherOrderNashStable`). The Nash clause covers
every keep-or-cancel choice for rejected proposals, which includes the paper's rule. -/
theorem theorem_3 {n : ℕ} (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ)
    (h : Stable S W P) : HigherOrderNashStable S W P := by sorry

end IncentiveFinNet.Supplement
