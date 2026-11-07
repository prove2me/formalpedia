-- Prove2me | Theorems.Thm_KSATWindow_eq_3_3
-- name    : KSATWindow.eq_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:27.604317+00:00
-- url     : https://prove2.me/theorems/e2f50869-8f28-4337-b48b-33128081c88a
-- title:
--   (3.3) — deletion identity $\beta_n(t)=2\,\mathbb E[\mathbf 1\{G\text{ sat}\}q_G(z)(1-q_G(z))]$
-- statement:
--   Fix $k\ge3$, $n>k$ and $t\ge0$, and put $z=kt/(2n)$. Let $G$ have the law of the Poisson-time formula $F_{n-1}((1-k/n)t)$ on $n-1$ variables. Then
--   $$\beta_n(t)=2\,\mathbb E\big[\mathbf 1\{G\text{ is satisfiable}\}\,q_G(z)\,(1-q_G(z))\big],$$
--   where $\beta_n(t)$ is the expected proportion of forced variables of $F_n(t)$ before unsatisfiability, and $q_G$ uses uniform signed $(k-1)$-clauses on the $n-1$ variables of $G$.
--
--   Deleting one variable turns "the variable is forced" into "exactly one of two independent perturbations of a common formula fails".
--
--   Differences from the source:
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
--   - encoding: E f(Fₙ(t)) for the Poisson-time formula Fₙ(t) = F_{n,Π_t} → the Poisson mixture Σ_m e^{−t}t^m/m!·E f(F_{n,m}) in [0,∞]; reason: this is what independence of Π_t and the clauses gives; every statement uses one time t only
--   - encoding: G formed by the clauses avoiding x, coupled with Fₙ(t) → the law of G only, as a Poisson mixture on n − 1 variables at time (1 − k/n)t; reason: (3.3) is an identity between numbers; the coupling enters only its proof
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7, eq. (3.3)

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

/-- **(3.3), p.7 — deletion identity.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7.

Fix `k ≥ 3`, `n > k` and `t ≥ 0`, and put `z = kt/(2n)`. Let `G` have the law of
`F_{n−1}((1 − k/n)t)`, the Poisson-time formula on `n − 1` variables. Then
`βₙ(t) = 2 E[1{G is satisfiable} q_G(z)(1 − q_G(z))]` (3.3), where `q_G` uses uniform signed
`(k−1)`-clauses on the `n − 1` variables of `G`.

**Formalization Note.** Both sides are Poisson mixtures (definition module `PoissonTime`); the
right side is the mixture over `n − 1` variables at time `(1 − k/n)t`. The identity is between
numbers, so no coupling of `G` with `Fₙ(t)` is stated. -/
theorem eq_3_3 (n k : ℕ) (hk : 3 ≤ k) (hkn : k < n) (t : ℝ) (ht : 0 ≤ t) :
    beta n k t =
      poissonMean (n - 1) k ((1 - (k : ℝ) / (n : ℝ)) * t) fun S =>
        if S.Nonempty then
          ENNReal.ofReal (2 * shortKill (n - 1) (k - 1) S ((k : ℝ) * t / (2 * (n : ℝ))) *
            (1 - shortKill (n - 1) (k - 1) S ((k : ℝ) * t / (2 * (n : ℝ)))))
        else 0 := by sorry

end KSATWindow
