-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_theorem_3_1
-- name    : HolonomicPositivity.Robust.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:36.45651+00:00
-- url     : https://prove2.me/theorems/f469cf78-8cd1-488f-aad2-bba9f7020780
-- title:
--   Theorem 3.1 — sufficient conditions for a robustly ultimately positive solution
-- statement:
--   Let $P,Q\in\mathbb R(x)$ have no poles on $\mathbb N$, and assume $Q(n)\ne0$ for all $n\in\mathbb N$. Suppose either of the following holds.
--
--   1. **(I)** $1\le\lim_{x\to\infty}P(x)\le\infty$ and $Q\ge-P$.
--   2. **(II)** $-\frac13-\frac1{9x^2}+O(x^{-3})\le P(x)<1-\frac2x+O(x^{-2})$ and $Q(x)\ge R_P(x)+O(x^{-d})$. With $P(x)=p_0+\frac{p_1}x+\frac{p_2}{x^2}+\frac{p_3}{x^3}+O(x^{-4})$ the Taylor expansion at infinity, $R_P$ and $d$ are:
--      - (II-1) if $p_0>-\frac13$: $R_P(x)=a^3-a^2-p_0a-\frac{p_1a}{x}-\frac{b}{x^2}$, $d=3$, where $a=\frac{1+\sqrt{1+3p_0}}3$ and $b=p_2a+\frac{(a+p_0+p_1)^2}{4\sqrt{1+3p_0}}$;
--      - (II-2) if $p_0=-\frac13$ and $p_1>0$: $R_P(x)=\frac1{27}-\frac{p_1}{3x}$, $d=2$;
--      - (II-3) if $(p_0,p_1)=(-\frac13,0)$: $R_P(x)=\frac1{27}-\frac{p_2}{3x^2}-\frac{c}{x^3}$, $d=4$, where $c=\frac{p_2+p_3}3+\frac2{81\sqrt3}(1+9p_2)^{3/2}$.
--
--   Then the recurrence
--
--   $$f(n+3)=f(n+2)+P(n)f(n+1)+Q(n)f(n)$$
--
--   admits a robustly ultimately positive solution: a solution $f$ and $\varepsilon>0$ such that every solution whose three initial values are within $\varepsilon$ of those of $f$ is ultimately positive.
--
--   The theorem applies in cases with a multiple dominant root, outside the scope of the classical simple-dominant-root criterion, and gives the explicit threshold $R_P$.
--
--   Differences from the source:
--   - encoding: the no-pole assumption on $P,Q$ is a global convention (PDF p.1) → explicit hypotheses on the reduced denominators; reason: Lean evaluates at a pole to a default value, and the source's convention covers all coefficients of the recurrence.
--   - encoding: $1\le\lim_{x\to\infty}P(x)\le\infty$ → a finite limit $\ell\ge1$ or divergence to $+\infty$; reason: a rational function has a limit in the extended reals, so the two alternatives are exactly this range.
--   - encoding: "small perturbations of the initial values" (PDF p.2) → a positive $\varepsilon$ bounding each of the three coordinate differences; reason: all norms on $\mathbb R^3$ define the same neighbourhoods.
--   - encoding: "let (7) be the Taylor expansion" → existentially quantified coefficients satisfying (7) inside condition (II); reason: under the two comparisons on $P$ the expansion exists and is unique, so no instance changes.
-- source:
--   Fugen Hagihara, STOC 2027 submission #328 (October 2026), Theorem 3.1, PDF p.5 (printed XX:5); recurrence (4) PDF p.4; robustness PDF p.2.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Recurrence
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

/-- Theorem 3.1, PDF p.5 (XX:5). `P` and `Q` have no poles on `ℕ` by the paper's global convention
(PDF p.1, line 38). -/
theorem theorem_3_1 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (h : ConditionI P Q ∨ ConditionII P Q) :
    AdmitsRobustlyUltimatelyPositiveSolution P Q := by sorry

end HolonomicPositivity.Robust
