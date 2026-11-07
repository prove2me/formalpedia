-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_1_block_balance
-- name    : MatroidEquitability.proof_theorem_1_block_balance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:01.857963+00:00
-- url     : https://prove2.me/theorems/2e537a5c-809c-457e-bc2f-5db7aa5fc5f2
-- title:
--   Proof of Theorem 1, the claim $|w(B'_i)-w(B'_j)|\le 1$ — a balanced block exists
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite block matroid and let $w\in[0,1]^E$. Then $M$ has a block $B$ with
--
--   $$
--   \bigl|w(B)-w(E\setminus B)\bigr|\le 1 .
--   $$
--
--   This is the bound that the proof of the main theorem applies to the union of a heaviest and a lightest base.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - encoding: a partition $E'=B'_i\sqcup B'_j$ into bases minimizing $|w(B'_i)-w(B'_j)|$ has value at most $1$ → some block `B` has $|w(B)-w(E\setminus B)|\le 1$; reason: the minimum over the finitely many blocks is at most $1$ exactly when some block attains a value at most $1$
--   - generalization: $M'=M|_{B_i\sqcup B_j}$ for two bases of $M$, with $\max_{e\in E}w_e=1$ → any finite block matroid with $w\in[0,1]^E$; reason: $M'$ is a finite block matroid and the scaled $w$ lies in $[0,1]^{E'}$
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 1, block-balance claim, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock

namespace MatroidEquitability

/-- The claim of the proof of Theorem 1: a block matroid with `w ∈ [0,1]^E` has a block `B` with
`|w(B) − w(E \ B)| ≤ 1` (printed p.10 = PDF p.12 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The page takes a minimizer of `|w(B) − w(E \ B)|` over the finitely many
blocks of the restriction `M' = M|_{B_i ⊔ B_j}`. A minimizer satisfies the bound exactly when some
block does, and any block matroid may play the role of `M'`. -/
theorem proof_theorem_1_block_balance {α : Type*} (M : Matroid α) [M.Finite] (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e ∧ w e ≤ 1) (hM : ∃ B, IsBlock M B) :
    ∃ B, IsBlock M B ∧ |setWeight w B - setWeight w (M.E \ B)| ≤ 1 := by sorry

end MatroidEquitability
