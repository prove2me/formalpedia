-- Prove2me | Theorems.Thm_KSATWindow_eq_2_5
-- name    : KSATWindow.eq_2_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:32:28.346204+00:00
-- url     : https://prove2.me/theorems/e2da4e47-779f-4fbf-9a13-3404d23fc6c3
-- title:
--   (2.5) — $\rho_j(H)=\binom{\ell(H)}{j}\big/\big(2^j\binom nj\big)$
-- statement:
--   Fix $k\ge3$, $n\ge k$ and a satisfiable formula $H$ on $[n]$; let $\ell(H)$ be its number of forced variables and $\rho_j(H)$ the probability that an independent uniform signed $j$-clause makes it unsatisfiable. For $1\le j\le k$,
--   $$\rho_j(H)=\frac{\binom{\ell(H)}{j}}{2^j\binom nj},$$
--   with $\binom bj=0$ when $b<j$.
--
--   The probability that one clause destroys a satisfiable formula is thus determined by a single integer, however complicated the solution set is.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5, eq. (2.5)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Forcing
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **(2.5), p.5 — exact kill probability.** G. Carenini, *A polynomial scaling window for random
k-SAT and a proof of the satisfiability conjecture*, STOC 2027 submission (manuscript sha256
1664cf10…), §2, p.5.

Fix `k ≥ 3`, `n ≥ k` and a satisfiable formula `H` on `[n]` with solution set `S ≠ ∅`; let
`b = ℓ(H)` be its number of forced variables. For `1 ≤ j ≤ k`,
`ρ_j(H) = C(b, j) / (2^j C(n, j))` (2.5), with `C(b, j) = 0` for `b < j`.

**Formalization Note.** `killRatio n b j` is the published `C(b,j)/(2^j C(n,j))`; `Nat.choose` is
`0` for `b < j`. -/
theorem eq_2_5 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k → rho n j S = killRatio n (forcedCount S) j := by sorry

end KSATWindow
