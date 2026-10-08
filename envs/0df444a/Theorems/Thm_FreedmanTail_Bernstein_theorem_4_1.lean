-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_theorem_4_1
-- name    : FreedmanTail.Bernstein.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:11:15.395261+00:00
-- url     : https://prove2.me/theorems/7e63f71c-7b09-45d3-b3ce-105c174b5075
-- title:
--   (4.1) Theorem — under (3.4), P{S_n ≥ a and T_n ≤ b for some n} ≤ (b/(a+b))^{a+b} e^a ≤ exp[−a²/(2(a+b))]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability triple, $\mathcal F_0\subset\mathcal F_1\subset\cdots$ an increasing sequence of sub-$\sigma$-fields of $\mathcal F$, and $X_1,X_2,\dots$ square-integrable random variables with $X_n$ $\mathcal F_n$-measurable. Let $S_n=X_1+\cdots+X_n$ and $T_n=V_1+\cdots+V_n$ with $V_n=\operatorname{Var}\{X_n\mid\mathcal F_{n-1}\}$. Suppose (3.4):
--   $$X_n\le1\ \text{a.e.}\quad\text{and}\quad E\{X_n\mid\mathcal F_{n-1}\}\le0\ \text{a.e.}\qquad\text{for all }n\ge1$$
--   (no lower bound on $X_n$). Then for any positive numbers $a$ and $b$,
--   $$P\{S_n\ge a\ \text{and}\ T_n\le b\ \text{for some } n=1,2,\dots\}\le\Bigl(\frac{b}{a+b}\Bigr)^{a+b}e^{a}\le\exp\Bigl[-\frac{a^{2}}{2(a+b)}\Bigr].$$
--
--   This is Freedman's inequality: a Bennett–Bernstein tail bound for supermartingales with increments bounded above, in which the deterministic variance of the independent case is replaced by the random intrinsic time $T_n$, and which holds simultaneously for all times $n$.
--
--   **Formalization Note** The event is the union over all $n\ge1$ (infinite horizon), and its probability is the measure of that set. $(b/(a+b))^{a+b}$ is a real power. Square integrability of each $X_n$ is assumed because $V_n$ is a conditional expectation, which Mathlib sets to $0$ for non-integrable arguments, and without it $T_n$ would silently be too small. This is the one hypothesis added to the page: (3.4) alone also allows increments of infinite (conditional) variance, for which the paper's $T_n$ is $+\infty$ on part of $\Omega$ and those points leave the event. The assumption narrows the class of processes; the conclusion is the page's, unchanged.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 107 (PDF p. 8), (4.1) Theorem

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (4.1) Theorem, p. 107: suppose (3.4). For any positive numbers `a`, `b`,
`P{S_n ≥ a and T_n ≤ b for some n = 1, 2, ⋯} ≤ (b/(a+b))^{a+b} e^a ≤ exp[−a²/(2(a+b))]`. -/
theorem theorem_4_1 {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a) ∧
      (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by sorry

end FreedmanTail.Bernstein
