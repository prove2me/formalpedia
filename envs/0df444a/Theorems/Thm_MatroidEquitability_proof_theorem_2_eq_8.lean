-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_8
-- name    : MatroidEquitability.proof_theorem_2_eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:30.785562+00:00
-- url     : https://prove2.me/theorems/1548601b-3dc4-4428-ab3b-3557e64cc22e
-- title:
--   Proof of Theorem 2, (8) — $|D\cap S|\ge|S|/2$
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite matroid, $u\in[0,1]^E$ and $S:=\{e\in E:u_e=1\}$. If $D$ is a block of $M$ and no block of $M$ has $u$-weight in the interval $(u(D),u(D)+1]$, then
--
--   $$
--   |D\cap S|\ge\frac{|S|}{2}. \tag{8}
--   $$
--
--   The page obtains this by "the symmetric argument", applying the exchange theorem to the pair $(E\setminus D,D)$.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - generalization: $D\in\mathcal H^-$, for $(u,\gamma)$ optimal in the program of the page with $\gamma>1$ → any block $D$ such that no block has $u$-weight in $(u(D),u(D)+1]$, any $u\in[0,1]^E$; reason: on the page $u(D)=d$ and every block has weight at most $d$ or at least $b>d+1$, which gives the hypothesis; it is the only property of $D$ the argument uses
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, (8), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock

namespace MatroidEquitability

/-- The claim (8) of the proof of Theorem 2: if `u ∈ [0,1]^E`, `S := {e ∈ E : u_e = 1}`, `D` is a block
and no block has `u`-weight in `(u(D), u(D) + 1]`, then `|D ∩ S| ≥ |S|/2` (printed p.9 = PDF p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** On the page `D ∈ H⁻`, so `u(D) = d`, and every block has weight at most `d` or
at least `b > d + 1`; this gives the gap hypothesis. The interval is not the mirror image of that of
(7): the page's symmetric argument takes the exchange for `(E \ D, D)`. -/
theorem proof_theorem_2_eq_8 {α : Type*} (M : Matroid α) [M.Finite] (u : α → ℝ)
    (hu : ∀ e ∈ M.E, 0 ≤ u e ∧ u e ≤ 1) (S : Set α) (hS : S = {e ∈ M.E | u e = 1}) (D : Set α)
    (hD : IsBlock M D)
    (hgap : ∀ C, IsBlock M C → ¬ (setWeight u D < setWeight u C ∧ setWeight u C ≤ setWeight u D + 1)) :
    (S.ncard : ℝ) / 2 ≤ ((D ∩ S).ncard : ℝ) := by sorry

end MatroidEquitability
