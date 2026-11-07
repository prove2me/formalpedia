-- Prove2me | Theorems.Thm_MatroidEquitability_theorem_2
-- name    : MatroidEquitability.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:08.056385+00:00
-- url     : https://prove2.me/theorems/6eba20db-eb13-4444-9c25-22e9a82d0d93
-- title:
--   Theorem 2 — consecutive block weights differ by at most $1$
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite block matroid and let $w\in[0,1]^E$. If $q_1<\dots<q_m$ are the distinct values in $\{w(B):B\text{ a block of }M\}$, then
--
--   $$
--   q_{s+1}-q_s\le 1\qquad\text{for all }s\in[m-1].
--   $$
--
--   This is the statement for block matroids from which the main theorem follows by repeated rebalancing.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - encoding: distinct values $q_1<\dots<q_m$ of the block weights and the bound on $q_{s+1}-q_s$ → blocks `B`, `D` with $w(B)<w(D)$ and no block weight strictly between, concluding $w(D)-w(B)\le 1$; reason: over a finite value set, consecutive values are exactly such pairs; the block matroid hypothesis is the existence of `B`
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 2, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock

namespace MatroidEquitability

/-- Theorem 2: for `w ∈ [0,1]^E`, two consecutive block weights of a block matroid differ by at most
`1` (printed p.7 = PDF p.9 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** "Consecutive values `q_s < q_{s+1}`" is: blocks `B, D` with `w(B) < w(D)` and
no block weight strictly between. The block matroid hypothesis is implied by the existence of `B`. -/
theorem theorem_2 {α : Type*} (M : Matroid α) [M.Finite] (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e ∧ w e ≤ 1) (B D : Set α) (hB : IsBlock M B) (hD : IsBlock M D)
    (hlt : setWeight w B < setWeight w D)
    (hcons : ∀ C, IsBlock M C → ¬ (setWeight w B < setWeight w C ∧ setWeight w C < setWeight w D)) :
    setWeight w D - setWeight w B ≤ 1 := by sorry

end MatroidEquitability
