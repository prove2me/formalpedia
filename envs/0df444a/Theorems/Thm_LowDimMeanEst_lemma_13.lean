-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_13
-- name    : LowDimMeanEst.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:40:08.882707+00:00
-- url     : https://prove2.me/theorems/8bc6aa8c-0fc6-48c6-9d6e-720825875023
-- title:
--   Lemma 13 — for all $c'>0$ there are $a$, $t'\ge\min(1,\sqrt{c'})$, $q_1',q_2'\ge0$ with $q_1'+q_2'-a/3-t'\sqrt2=-1$ and the exponential-quadratic inequality (24)
-- statement:
--   **Lemma 13.** There are functions $a(c'),t'(c'),q_1'(c'),q_2'(c')$ of $c'>0$ and universal constants $T>0$, $A_0>0$ such that for every $c'>0$: $t'\ge\min(1,\sqrt{c'})$, $q_1',q_2'\ge0$,
--
--   $$q_1'+q_2'-\frac a3-t'\sqrt2=-1,$$
--
--   and for all $z\ge0$ and $x\in\mathbb R$,
--
--   $$1+t'x+\frac{q_1'}{c'}z+q_2'x^2\ \ge\ e^{\,a+(-a+z-c'x^2+t'x)(1-\min(1,z))}. \tag{24}$$
--
--   Moreover $t'\le T$, $a\ge-A_0$, and $a$ is a non-increasing function of $c'$.
--
--   This is the satisfiability problem to which the moment generating function bound of Lemma 12 reduces; it certifies that the dual program has value $-1$, which yields the constant $\sqrt2$ of the main theorem.
--
--   **Formalization Note** "Non-increasing function in $c'$" is antitone on $(0,\infty)$; the "universal constant" upper bound on $t'$ and negative lower bound on $a$ are $T$ and $-A_0$.
--
--   Differences from the source:
--   - encoding: parameters a, t′, q′₁, q′₂ for each c′; a a function of c′ → functions of c′ quantified first, with constants T, A₀; reason: the Moreover clause speaks of a as a function of c′; same content
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 13, p.21 (restated p.53; proof Appendix C, pp.53–82)

import Mathlib

namespace LowDimMeanEst

/-- **Lemma 13**, p.21 (restated p.53; proof in Appendix C, pp.53–82).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"For all c′ > 0, there exist parameters a ∈ ℝ, t′ ≥ min(1, √c′), and q′₁, q′₂ ≥ 0 such that
q′₁ + q′₂ − a/3 − t′√2 = −1 and
∀_{z≥0, x∈ℝ} 1 + t′x + (q′₁/c′) z + q′₂x² ≥ e^{a+(−a+z−c′x²+t′x)(1−min(1,z))}. (24)
Moreover, t′ is bounded above by a universal constant, a is a non-increasing function in c′, and a
is lower bounded by a negative universal constant."

**Formalization Note.** The parameters are functions `a, t′, q′₁, q′₂` of `c′` (the "Moreover" clause
speaks of `a` as a function of `c′`); `T` is the universal upper bound on `t′` and `−A0`, `A0 > 0`,
the negative universal lower bound on `a`. "Non-increasing" is `AntitoneOn a (0, ∞)`.
-/
theorem lemma_13 :
    ∃ (a t' q1 q2 : ℝ → ℝ) (T A0 : ℝ), 0 < T ∧ 0 < A0 ∧ AntitoneOn a (Set.Ioi 0) ∧
      ∀ c : ℝ, 0 < c →
        min 1 (Real.sqrt c) ≤ t' c ∧ 0 ≤ q1 c ∧ 0 ≤ q2 c ∧
        q1 c + q2 c - a c / 3 - t' c * Real.sqrt 2 = -1 ∧
        (∀ z x : ℝ, 0 ≤ z →
          Real.exp (a c + (-a c + z - c * x ^ 2 + t' c * x) * (1 - min 1 z)) ≤
            1 + t' c * x + q1 c / c * z + q2 c * x ^ 2) ∧
        t' c ≤ T ∧ -A0 ≤ a c := by sorry

end LowDimMeanEst
