-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_4
-- name    : LostSalesBalancing.DualBalancing.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:22.18225+00:00
-- url     : https://prove2.me/theorems/28f3ef49-bcac-44af-bede-249d1dcabb73
-- title:
--   Lemma 3.4 — properties of the alternation event A_st
-- statement:
--   On one nonnegative demand path, compare nonnegative order sequences $B$ and $P$. For $1\le t\le s<t+L\le T$, let $A_{st}$ mean $Y^B_{st}<Y^P_{st}$ but $Y^B_{s+1,t}\ge Y^P_{s+1,t}$, and put $\Delta Q_s=\sum_{j=s+1-L}^{t}(Q_j^B-Q_j^P)$. Then:
--
--   1. $A_{st}$ implies $\Delta Q_s\ge0$.
--   2. $A_{st}$ implies $I_s^P>I_s^B+\Delta Q_s$.
--   3. $A_{st}$ is equivalent to $Y^B_{st}<Y^P_{st}$, $\Delta Q_s\ge0$, and $d_s\ge I_s^P-\Delta Q_s$ together.
--   4. $A_{st}$ implies positive lost demand under $B$ in period $s$, and any positive lost demand under $B$ implies $I^B_{s+1}=Q^B_{s+1-L}$.
--
--   The crossing description identifies the inventory depletion event used in the paper's conditional comparisons.
--
--   **Formalization Note** The paper prints the threshold in (iii) as $d_s>I_s^P-\Delta Q_s$, but equality already permits a crossing: the next truncated positions may tie. The statement uses the mathematically correct weak threshold $d_s\ge I_s^P-\Delta Q_s$. The paper phrases clause (iv) as $\Pi^B_{s-L}>0$. Since the broader cost regime permits $p_s=0$, the statement uses $(d_s-I_s^B)^+>0$, the precise physical fact in the proof. Pipeline orders for $j\le0$ are common to both sequences.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript p. 15, §3.2, Lemma 3.4

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset LeviBalancing.DualBalancing

/-- Lemma 3.4, all four clauses, for the alternation event `A_st`. Positive lost units replace
positive penalty when the nonnegative penalty rate is allowed to vanish. -/
theorem lemma_3_4 (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j)
    (t s : ℤ) (ht : 1 ≤ t) (hs : t ≤ s) (hst : s < t + I.L)
    (hT : t + I.L ≤ (I.T : ℤ)) :
    let ΔQ := (∑ j ∈ Icc (s + 1 - I.L) t, order I.toInstance QB j) -
      (∑ j ∈ Icc (s + 1 - I.L) t, order I.toInstance QP j)
    let A := truncPos I d QB s t < truncPos I d QP s t ∧
      truncPos I d QP (s + 1) t ≤ truncPos I d QB (s + 1) t
    (A ↔ truncPos I d QB s t < truncPos I d QP s t ∧ 0 ≤ ΔQ ∧
      onHand I d QP s - ΔQ ≤ d s) ∧
    (A → 0 ≤ ΔQ ∧ onHand I d QB s + ΔQ < onHand I d QP s ∧
      0 < lostUnits I d QB s ∧
      onHand I d QB (s + 1) = order I.toInstance QB (s + 1 - I.L)) ∧
    (0 < lostUnits I d QB s →
      onHand I d QB (s + 1) = order I.toInstance QB (s + 1 - I.L)) := by sorry

end LostSalesBalancing.DualBalancing
