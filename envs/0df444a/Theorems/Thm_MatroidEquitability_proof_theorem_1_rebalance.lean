-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_1_rebalance
-- name    : MatroidEquitability.proof_theorem_1_rebalance
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:32:13.020724+00:00
-- url     : https://prove2.me/theorems/d6f969aa-4aa2-4a9f-93dd-60c42ec39002
-- title:
--   Proof of Theorem 1, the rebalancing step — the maximum drops, or fewer bases attain it
-- statement:
--   Let $M$ be a finite matroid, $w$ any weights, and $E=B_1\sqcup\dots\sqcup B_k$ a partition into bases. Let $B_i$ have the maximum weight and $B_j$ the minimum weight among the $k$ bases, with $w(B_i)-w(B_j)>1$, and put $E':=B_i\cup B_j$. Let $B'$ be a block of $M':=M|_{E'}$ with $|w(B')-w(E'\setminus B')|\le 1$. Then
--
--   1. $B_i$ is a block of $M'$;
--   2. replacing $B_i$ by $B'$ and $B_j$ by $E'\setminus B'$ gives again a partition of $E$ into bases of $M$;
--   3. after this replacement, either $\max_t w(B_t)$ decreases, or $\max_t w(B_t)$ remains the same but the number of bases attaining the maximum weight decreases.
--
--   Since there are finitely many partitions, iterating this step terminates, which gives the main theorem.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - generalization: $w\ge 0$ scaled so that $\max_{e\in E}w_e=1$, and $B'_i$ a minimizer of the imbalance → any $w$ and any block `B'` of imbalance at most $1$; reason: the step uses only the imbalance bound and the gap above $1$; the page's choices satisfy both by `proof_theorem_1_block_balance`
--   - encoding: "Consider the block matroid $M'$", "we replace the partition", and $\max_t w(B_t)$ → explicit conclusions that `B i` is a block of $M'$ and the new family is a base partition; the new maximum as an `IsGreatest` witness `m'`, the old one as $w(B_i)$; counts as `ncard` on `Fin k`; reason: these make explicit what the sentence takes for granted; the same claim
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 1, rebalancing step, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBasePartition
import Definitions.Def_MatroidEquitability_IsBlock

namespace MatroidEquitability

/-- The rebalancing step of the proof of Theorem 1: for a heaviest base `B_i` and a lightest base `B_j`
with `w(B_i) − w(B_j) > 1`, `B_i` is a block of `M' = M|_{B_i ⊔ B_j}`, and replacing `B_i ⊔ B_j` by a
block `B'` of `M'` and its complement in `E' = B_i ⊔ B_j`, with `|w(B') − w(E' \ B')| ≤ 1`, gives again
a partition into bases, in which either the maximum base weight decreases, or it stays the same and
fewer bases attain it (printed p.10 = PDF p.12 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The maximum of the new family is an `IsGreatest` witness `m'`; the maximum of
the old family is `w(B_i)`. Counts are `ncard` on subsets of `Fin k`. No range hypothesis on `w`. -/
theorem proof_theorem_1_rebalance {α : Type*} (M : Matroid α) [M.Finite] {k : ℕ} (w : α → ℝ)
    (B : Fin k → Set α) (hB : IsBasePartition M B) (i j : Fin k)
    (hi : ∀ t, setWeight w (B t) ≤ setWeight w (B i))
    (hj : ∀ t, setWeight w (B j) ≤ setWeight w (B t))
    (hgap : 1 < setWeight w (B i) - setWeight w (B j)) (B' : Set α)
    (hB' : IsBlock (M.restrict (B i ∪ B j)) B')
    (hbal : |setWeight w B' - setWeight w ((B i ∪ B j) \ B')| ≤ 1) :
    IsBlock (M.restrict (B i ∪ B j)) (B i) ∧
    IsBasePartition M (Function.update (Function.update B i B') j ((B i ∪ B j) \ B')) ∧
    ∃ m', IsGreatest (Set.range fun t =>
          setWeight w (Function.update (Function.update B i B') j ((B i ∪ B j) \ B') t)) m' ∧
      (m' < setWeight w (B i) ∨
        (m' = setWeight w (B i) ∧
          {t | setWeight w (Function.update (Function.update B i B') j ((B i ∪ B j) \ B') t) = m'}.ncard
            < {t | setWeight w (B t) = setWeight w (B i)}.ncard)) := by sorry

end MatroidEquitability
