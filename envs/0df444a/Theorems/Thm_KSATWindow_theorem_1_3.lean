-- Prove2me | Theorems.Thm_KSATWindow_theorem_1_3
-- name    : KSATWindow.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:56.247195+00:00
-- url     : https://prove2.me/theorems/d3c5ff27-61e1-4793-9fae-549d4ad4a3fa
-- title:
--   Theorem 1.3 — $\operatorname{Var}(T_n)\le C_kn^{1+2/k}$ and $\mathbb P(|T_n-a_n|\ge x)\le\min\{1,C_kn^{1+2/k}/x^2\}$
-- statement:
--   For every fixed $k\ge3$ there exists $C_k<\infty$ such that for every $n\ge k$
--   $$\operatorname{Var}(T_n)\le C_k\,n^{1+2/k},$$
--   and consequently, for every $x>0$,
--   $$\mathbb P(|T_n-a_n|\ge x)\le\min\Big\{1,\frac{C_k\,n^{1+2/k}}{x^2}\Big\},$$
--   where $T_n$ is the first unsatisfiable clause count of random $k$-SAT on $n$ variables and $a_n=\mathbb E T_n$.
--
--   This is the paper's main estimate; Theorem 1.1 follows from it by Chebyshev's inequality. A stronger variance bound, $C\,n\,\ell(k,n)$, is on the platform as `OAI.RandomKSAT.variance_main`.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: Var(Tₙ) → evariance of H in [0,∞]; reason: no junk value: the bound also asserts finiteness
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §1, p.2, Theorem 1.3

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

/-- **Theorem 1.3, p.2 — variance and tail of the first unsatisfiable count.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §1, p.2.

For every fixed `k ≥ 3` there is `C_k < ∞` such that for every `n ≥ k`,
`Var(Tₙ) ≤ C_k n^{1+2/k}`, and consequently, for every `x > 0`,
`P(|Tₙ − aₙ| ≥ x) ≤ min{1, C_k n^{1+2/k}/x²}`.

**Formalization Note.** `Var(Tₙ)` is `evariance H` in `[0, ∞]`, so the bound also asserts that
the variance is finite. One constant serves both clauses. -/
theorem theorem_1_3 (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ, k ≤ n →
      evariance (H : Stream n k → ℝ) (streamLaw n k) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (1 + (2 : ℝ) / (k : ℝ))) ∧
        ∀ x : ℝ, 0 < x →
          (streamLaw n k).real {ω | x ≤ |H ω - meanTime n k|} ≤
            min 1 (C * (n : ℝ) ^ (1 + (2 : ℝ) / (k : ℝ)) / x ^ 2) := by sorry

end KSATWindow
