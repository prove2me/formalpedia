-- Prove2me | Theorems.Thm_OnePointComplexity_Dictionary_theorem_2_3
-- name    : OnePointComplexity.Dictionary.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:51.728588+00:00
-- url     : https://prove2.me/theorems/b128a4c3-7549-428f-b84b-6695c453285e
-- title:
--   Theorem 2.3 — complete one-point extraction (corrected: degree zero retained)
-- statement:
--   Let $I$ have a nonempty feasible family and positive integer element costs. Write $y_I=|E|\ln2/(2\pi)$ and $\widetilde y_I=(|E|+2)\ln2/\pi$.
--
--   1. For every real $y>0$ with $y\ge y_I$,
--
--   $$\mathrm{OPT}=\left\lceil-\frac{\ln\Theta_I(iy)}{2\pi y}\right\rceil.$$
--
--   2. For every real $y\ge\widetilde y_I$ and every real $a$ with $\Theta_I(iy)/2\le a\le2\Theta_I(iy)$, set $v=-\ln a/(2\pi y)$. Then
--
--   $$|v-\mathrm{OPT}|\le\frac12-\frac{\ln2}{2\pi y}.$$
--
--   In particular OPT is the unique nearest integer, with the displayed positive margin. Explicitly, for each other integer $k$, its distance from $v$ is at least $|v-\mathrm{OPT}|+\ln2/(2\pi y)$.
--
--   3. For any directed graph on $n$ vertices with positive arc costs, any feasible Hamiltonian tour $T$, and every real $y\ge\widetilde y_n=\ln(2n!)/\pi$,
--
--   $$T\text{ is optimal}\iff e^{2\pi c(T)y}\Theta_I(iy)\le(n-1)!.$$
--
--   If $T$ is not optimal, the scalar on the left of the inequality is at least $n!$. Tours are single-cycle permutations, counted once, and the graph need not be complete.
--
--   The result extracts an integer optimum from one real value and supplies a numerical tour optimality certificate. All three parts are retained.
--
--   Differences from the source:
--   - correction: equation (1) writes the coefficient sum over k≥1 → the cost polynomial and series include k=0 and permit OPT=0; reason: E={e}, c(e)=1, and the feasible family={∅} satisfy every source assumption but give series 1 instead of the printed sum 0; the defining feasible-set sum fixes the intended object
--   - encoding: the series is evaluated on the positive imaginary axis and its real-valued factor-two approximations → y>0 is explicit in (a), and Factor records positivity as well as both inequalities in (b); reason: the standing upper-half-plane domain excludes division by zero; nonempty positive exponential sums imply these positivity clauses
--   - encoding: OPT is the nearest integer with margin ln(2)/(2πy), and tours are directed Hamiltonian cycles → a distance comparison against every other integer, and single-orbit permutations on Fin n with an actual-tour hypothesis; reason: the same rounding margin is explicit; the actual tour ensures n≥1 and the factorial bounds count each cycle once
-- source:
--   Varsha Gupta, STOC 2027 submission #1733 (October 2026), Theorem 2.3(a)–(c), printed p. 4 (PDF p. 5), proof continuing on printed p. 5 (PDF p. 6)

import Definitions.Def_OnePointComplexity_Dictionary_FiniteSeries

set_option autoImplicit false

namespace OnePointComplexity.Dictionary

/-- Theorem 2.3(a)-(c), printed pp.4-5 (PDF 5-6). Real positive heights in (a),
all admissible real approximations in (b), and arbitrary digraphs in (c). -/
theorem theorem_2_3 :
    (∀ (I : Instance), I.feasible.Nonempty →
      (∀ y : ℝ, 0 < y → extractionHeight I ≤ y →
        (optimum I : ℤ) = ⌈-Real.log (thetaImag I y) / (2 * Real.pi * y)⌉) ∧
      (∀ y a : ℝ, evaluationHeight I ≤ y → Factor 2 (thetaImag I y) a →
        let v := -Real.log a / (2 * Real.pi * y)
        |v - (optimum I : ℝ)| ≤ 1 / 2 - Real.log 2 / (2 * Real.pi * y) ∧
        (∀ k : ℤ, k ≠ (optimum I : ℤ) →
          |v - (optimum I : ℝ)| + Real.log 2 / (2 * Real.pi * y) ≤ |v - (k : ℝ)|))) ∧
    (∀ (n : ℕ) (G : TourInstance n) (σ : Equiv.Perm (Fin n)) (y : ℝ),
      IsTour G σ → tourHeight n ≤ y →
      (IsOptimalTour G σ ↔
        Real.exp (2 * Real.pi * (tourCost G σ : ℝ) * y) * tourTheta G y ≤
          ((n - 1).factorial : ℝ)) ∧
      (¬ IsOptimalTour G σ → (n.factorial : ℝ) ≤
        Real.exp (2 * Real.pi * (tourCost G σ : ℝ) * y) * tourTheta G y)) := by sorry

end OnePointComplexity.Dictionary
