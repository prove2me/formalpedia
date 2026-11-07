-- Prove2me | Theorems.Thm_KSATWindow_lemma_2_1
-- name    : KSATWindow.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:28.537723+00:00
-- url     : https://prove2.me/theorems/ea548451-fe9b-4e3f-bf50-9f2f058fb365
-- title:
--   Lemma 2.1 — replacement: $q_G(z)\le C_{k,L}\,r_n(G)^{-(k-1)/k}$ for $0\le z\le L$
-- statement:
--   Fix $k\ge3$ and $L<\infty$. There is a constant $C_{k,L}$, depending only on $k$ and $L$, such that for every $n\ge k$, every satisfiable formula $G$ on $[n]$ and every $0\le z\le L$,
--   $$q_G(z)\le C_{k,L}\,r_n(G)^{-(k-1)/k},$$
--   where $q_G(z)$ is the probability that adjoining an independent Poisson number of mean $z$ of uniform signed $(k-1)$-clauses makes $G$ unsatisfiable, and $r_n(G)$ is the remaining expected time of $G$ under uniform $k$-clauses.
--
--   A formula that $k$-clauses take long to destroy is also hard to destroy with a bounded number of shorter clauses. This is the form of replacement used in the deletion argument of §3.
--
--   Differences from the source:
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.6, Lemma 2.1, eq. (2.7)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Forcing
import Definitions.Def_KSATWindow_PoissonTime
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **Lemma 2.1, p.6 — replacement of shorter clauses.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.6.

Fix `k ≥ 3` and `L < ∞`. There is a constant `C_{k,L}` such that for every `n ≥ k`, every
satisfiable formula `G` on `[n]` (solution set `S ≠ ∅`) and every `0 ≤ z ≤ L`,
`q_G(z) ≤ C_{k,L} rₙ(G)^{−(k−1)/k}` (2.7), where `q_G(z)` is the probability that adjoining an
independent Poisson number of mean `z` of uniform signed `(k−1)`-clauses makes `G` unsatisfiable.

**Formalization Note.** The constant is chosen after `k` and `L` and before `n`, `S`, `z`.
`rₙ(G) = lifetime n k S ≥ 1` for `S ≠ ∅` ((2.3)), so the real power is of a positive number. -/
theorem lemma_2_1 (k : ℕ) (hk : 3 ≤ k) (L : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, k ≤ n → ∀ S : Finset (Assignment n), S.Nonempty →
      ∀ z : ℝ, 0 ≤ z → z ≤ L →
        shortKill n (k - 1) S z ≤ C * lifetime n k S ^ (-(((k : ℝ) - 1) / (k : ℝ))) := by sorry

end KSATWindow
