-- Prove2me | Theorems.Thm_KSATWindow_eq_2_3_2_4
-- name    : KSATWindow.eq_2_3_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:34.416206+00:00
-- url     : https://prove2.me/theorems/3e29d02b-1c02-49c2-84f3-6e37eabdb335
-- title:
--   (2.3)–(2.4) — $1\le r_n(G)\le a_n\le 2^k(n\log2+1)$ and $\mathbb E[r_n(G\wedge C)]=r_n(G)-1$
-- statement:
--   Fix $k\ge3$ and $n\ge k$. For a satisfiable formula $G$ on $[n]$ (not necessarily a $k$-CNF), let $r_n(G)$ be its remaining expected time: the expected number of further independent uniform signed $k$-clauses needed to make it unsatisfiable, with $r_n=0$ on unsatisfiable formulas. Then
--   $$1\le r_n(G)\le a_n\le 2^k(n\log 2+1),\qquad(2.3)$$
--   $$\mathbb E[r_n(G\wedge C)]=r_n(G)-1,\qquad(2.4)$$
--   where $a_n=\mathbb E\,T_n$ and $C$ is a uniform member of $\mathcal C_n$.
--
--   The identity (2.4) is the exact drift of the remaining time, the basis of the occupation estimate Lemma 3.1; (2.3) gives $r_n=O_k(n)$.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
--   - encoding: rₙ(G) = E min{m ≥ 1 : G ∧ C₁ ∧ ⋯ ∧ C_m unsatisfiable} → lifetime n k S = Σ_{m≥0} P(S survives m uniform clauses) (published); reason: the tail-sum formula for the mean of a positive integer variable; both are 0 at S = ∅
--   - encoding: E over a uniform C ∈ Cₙ → favg, the average over all of Clause n k; reason: uniform law on a finite set
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5, eqs. (2.3), (2.4)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Window
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **(2.3), (2.4), p.5 — bounds and first step of the remaining expected time.**
G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5.

Fix `k ≥ 3`, `n ≥ k` and a satisfiable formula `G` on `[n]` with solution set `S ≠ ∅`. Its
remaining expected time `rₙ(G)` is `lifetime n k S`. Then
`1 ≤ rₙ(G) ≤ aₙ ≤ 2^k(n log 2 + 1)` (2.3), and, for a uniform `C ∈ Cₙ`,
`E[rₙ(G ∧ C)] = rₙ(G) − 1` (2.4), where `rₙ` of an unsatisfiable formula is `0`.

**Formalization Note.** `lifetime n k S = Σ_{m≥0} P(S survives m independent uniform k-clauses)`,
which is `E min{m ≥ 1 : G ∧ C₁ ∧ ⋯ ∧ C_m unsatisfiable}` for `S ≠ ∅` and `0` at `S = ∅` (the
paper's convention). The solution set of `G ∧ C` is `S.filter (Satisfies C)`, and `favg` is the
average over all `C ∈ Cₙ`. -/
theorem eq_2_3_2_4 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    (1 ≤ lifetime n k S ∧ lifetime n k S ≤ meanTime n k ∧
      meanTime n k ≤ (2 : ℝ) ^ k * ((n : ℝ) * Real.log 2 + 1)) ∧
    favg (fun c : Clause n k => lifetime n k (S.filter (Satisfies c))) = lifetime n k S - 1 := by sorry

end KSATWindow
