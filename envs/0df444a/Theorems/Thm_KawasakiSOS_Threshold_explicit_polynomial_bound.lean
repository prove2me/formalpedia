-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_explicit_polynomial_bound
-- name    : KawasakiSOS.Threshold.explicit_polynomial_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:42.654852+00:00
-- url     : https://prove2.me/theorems/17d431c1-d596-479f-bcc9-a9dbeef296b9
-- title:
--   Theorem 1.2: the explicit polynomial bound
-- statement:
--   There is an absolute constant $C>0$ such that for all $\lambda>1$, $5\le k\le n$ and $\varepsilon\in(0,1)$,
--
--   $$\tau(\varepsilon)\le C\,\lambda^4k^6n^{10}\Bigl(n(1+\log\lambda)+\log\frac1\varepsilon\Bigr).$$
--
--   The constant does not depend on $\lambda$. The bound has no exponential dependence on $k$, which is the quantitative content of the upper half of the threshold. The source's closing sentence, that the mixing time is polynomial for fixed $\lambda$, is clause (ii) of the goal theorem.
--
--   Differences from the source:
--   - reading: "τ(ε) = O(λ⁴k⁶n¹⁰(n(1 + log λ) + log(1/ε)))" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
--   - encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty; reason: Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free
--   - reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain; reason: the source does not define the term; this is the standard meaning, as in its reference [LPW17]
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 1.2, p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_tau
import Definitions.Def_KawasakiSOS_Threshold_mixingSet

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 1.2, p. 3 (PDF p. 4).

Formalization Notes:
- reading: "τ(ε) = O(λ⁴k⁶n¹⁰(n(1 + log λ) + log(1/ε)))" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters.
- encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty. Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free.
- reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain. The source does not define the term; this is the standard meaning, as in its reference [LPW17]. -/
theorem explicit_polynomial_bound : ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 < lam → ∀ (n k : ℕ) [NeZero k], 5 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
    (mixingSet n k lam ε).Nonempty ∧
      (tau n k lam ε : ℝ) ≤ C * lam ^ 4 * (k : ℝ) ^ 6 * (n : ℝ) ^ 10 *
        ((n : ℝ) * (1 + Real.log lam) + Real.log (1 / ε)) := by sorry

end KawasakiSOS.Threshold
