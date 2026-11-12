-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_7
-- name    : MatroidEquitability.proof_theorem_2_eq_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:31:39.671813+00:00
-- url     : https://prove2.me/theorems/32b8495d-cae4-4f49-8fc7-6e6617eed18c
-- title:
--   Proof of Theorem 2, (7) — $|B\cap S|\le|S|/2$
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite matroid, $u\in[0,1]^E$ and $S:=\{e\in E:u_e=1\}$. If $B$ is a block of $M$ and no block of $M$ has $u$-weight in the interval $[u(B)-1,u(B))$, then
--
--   $$
--   |B\cap S|\le\frac{|S|}{2}. \tag{7}
--   $$
--
--   Together with its counterpart (8) and the identity (6), this forces the value of the gap program to be nonpositive.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - generalization: $B\in\mathcal H^+$, for $(u,\gamma)$ optimal in the program of the page with $\gamma>1$ → any block $B$ such that no block has $u$-weight in $[u(B)-1,u(B))$, any $u\in[0,1]^E$; reason: on the page $u(B)=b$ and every block has weight at least $b$ or at most $d<b-1$, which gives the hypothesis; it is the only property of $B$ the page's argument uses
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, (7), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock

namespace MatroidEquitability

/-- The claim (7) of the proof of Theorem 2: if `u ∈ [0,1]^E`, `S := {e ∈ E : u_e = 1}`, `B` is a block
and no block has `u`-weight in `[u(B) − 1, u(B))`, then `|B ∩ S| ≤ |S|/2` (printed p.9 = PDF p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** On the page `B ∈ H⁺`, so `u(B) = b`, and every block has weight at least `b`
or at most `d < b − 1`; this gives the gap hypothesis, the only property of `B` the argument uses. -/
theorem proof_theorem_2_eq_7 {α : Type*} (M : Matroid α) [M.Finite] (u : α → ℝ)
    (hu : ∀ e ∈ M.E, 0 ≤ u e ∧ u e ≤ 1) (S : Set α) (hS : S = {e ∈ M.E | u e = 1}) (B : Set α)
    (hB : IsBlock M B)
    (hgap : ∀ C, IsBlock M C → ¬ (setWeight u B - 1 ≤ setWeight u C ∧ setWeight u C < setWeight u B)) :
    ((B ∩ S).ncard : ℝ) ≤ (S.ncard : ℝ) / 2 := by sorry

end MatroidEquitability
