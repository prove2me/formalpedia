-- Prove2me | Theorems.Thm_KSATWindow_eq_2_6
-- name    : KSATWindow.eq_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:28.481334+00:00
-- url     : https://prove2.me/theorems/988f3352-9e62-43ce-b564-075bd6422718
-- title:
--   (2.6) — $\rho_k(H)\ge 2^{1-k}\rho_{k-1}(H)^{k/(k-1)}-\big((k-1)/(2n)\big)^k$
-- statement:
--   Fix $k\ge3$, $n\ge k$ and a satisfiable formula $H$ on $[n]$. Then
--   $$\rho_k(H)\ \ge\ 2^{1-k}\,\rho_{k-1}(H)^{k/(k-1)}-\Big(\frac{k-1}{2n}\Big)^k.$$
--
--   This compares the killing power of $(k-1)$-clauses and $k$-clauses at every satisfiable formula: up to a finite-size error, $\rho_k$ is at least a constant times the $k/(k-1)$-th power of $\rho_{k-1}$. It is the pointwise input of the replacement lemma (Lemma 2.1).
--
--   Differences from the source:
--   - encoding: a satisfiable formula H → its nonempty solution set S; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.6, eq. (2.6)

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

/-- **(2.6), p.6 — comparison of `ρ_k` with `ρ_{k−1}`.** G. Carenini, *A polynomial scaling
window for random k-SAT and a proof of the satisfiability conjecture*, STOC 2027 submission
(manuscript sha256 1664cf10…), §2, pp.5–6.

Fix `k ≥ 3`, `n ≥ k` and a satisfiable formula `H` on `[n]` with solution set `S ≠ ∅`. Then
`ρ_k(H) ≥ 2^{1−k} ρ_{k−1}(H)^{k/(k−1)} − ((k−1)/(2n))^k` (2.6).

**Formalization Note.** Powers with real exponents are `Real.rpow` of nonnegative bases;
`k − 1` is a natural number, safe at `k ≥ 3`. -/
theorem eq_2_6 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    (2 : ℝ) ^ (1 - (k : ℝ)) * rho n (k - 1) S ^ ((k : ℝ) / ((k : ℝ) - 1)) -
        (((k : ℝ) - 1) / (2 * (n : ℝ))) ^ k ≤ rho n k S := by sorry

end KSATWindow
