-- Prove2me | Theorems.Thm_KSATWindow_lemma_3_1
-- name    : KSATWindow.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:54.997201+00:00
-- url     : https://prove2.me/theorems/0557f9cb-6ed6-46e3-932e-4d6150142830
-- title:
--   Lemma 3.1 — $\sum_m\mathbb E[\mathbf 1\{T_n>m\}r_n(F_{n,m})^{-\lambda}]\le 2^\lambda\int_0^{a_n}(1+x)^{-\lambda}dx$, with its three orders
-- statement:
--   For every $\lambda>0$, every $k\ge3$ and every $n\ge k$,
--   $$\sum_{m\ge0}\mathbb E\big[\mathbf 1\{T_n>m\}\,r_n(F_{n,m})^{-\lambda}\big]\ \le\ 2^\lambda\int_0^{a_n}(1+x)^{-\lambda}\,dx,\qquad(3.1)$$
--   where the summand is $0$ at an unsatisfiable formula. Moreover the right-hand side is
--
--   1. $O_\lambda(a_n^{1-\lambda})$ for $0<\lambda<1$;
--   2. $O(\log(1+a_n))$ for $\lambda=1$;
--   3. $O_\lambda(1)$ for $\lambda>1$;
--
--   with constants depending on $\lambda$ only.
--
--   The occupation sum of inverse powers of the remaining time is as small as if $r_n$ decreased deterministically by one per clause, although it need not.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: 1{Tₙ > m} → F_{n,m} is satisfiable (its solution set is nonempty); reason: the two events are equal
--   - reading: the right-hand side is O_λ(·) (as n → ∞) → one constant C(λ) bounding the right-hand side for every k ≥ 3 and every n ≥ k; reason: O_λ names λ as the only dependence; the bounds hold for every value aₙ ≥ 0, so no threshold in n is needed
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7, Lemma 3.1, eq. (3.1)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Window
import Definitions.Def_KSATWindow_Forcing
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **Lemma 3.1, p.7 — occupation sum of inverse powers of the remaining time.**
G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7.

For every `λ > 0`, every `k ≥ 3` and every `n ≥ k`,
`Σ_{m≥0} E[1{Tₙ > m} rₙ(F_{n,m})^{−λ}] ≤ 2^λ ∫₀^{aₙ} (1 + x)^{−λ} dx` (3.1).
The right-hand side is `O_λ(aₙ^{1−λ})` for `0 < λ < 1`, `O(log(1 + aₙ))` for `λ = 1`, and
`O_λ(1)` for `λ > 1`; each constant depends on `λ` only.

**Formalization Note.** `1{Tₙ > m}` is "`F_{n,m}` is satisfiable", i.e. its solution set is
nonempty; the summand is `0` at an unsatisfiable formula (the indicator convention of p.7). The
left side is a sum in `ℝ≥0∞`. -/
theorem lemma_3_1 (lam : ℝ) (hlam : 0 < lam) :
    (∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n →
      ∑' m : ℕ, ∫⁻ ω, (if (solutions ω m).Nonempty then
          ENNReal.ofReal (lifetime n k (solutions ω m) ^ (-lam)) else 0) ∂(streamLaw n k) ≤
        ENNReal.ofReal ((2 : ℝ) ^ lam * ∫ x in (0 : ℝ)..meanTime n k, (1 + x) ^ (-lam))) ∧
    (lam < 1 → ∃ C : ℝ, ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n →
      (2 : ℝ) ^ lam * ∫ x in (0 : ℝ)..meanTime n k, (1 + x) ^ (-lam) ≤
        C * meanTime n k ^ (1 - lam)) ∧
    (lam = 1 → ∃ C : ℝ, ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n →
      (2 : ℝ) ^ lam * ∫ x in (0 : ℝ)..meanTime n k, (1 + x) ^ (-lam) ≤
        C * Real.log (1 + meanTime n k)) ∧
    (1 < lam → ∃ C : ℝ, ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n →
      (2 : ℝ) ^ lam * ∫ x in (0 : ℝ)..meanTime n k, (1 + x) ^ (-lam) ≤ C) := by sorry

end KSATWindow
