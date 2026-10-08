-- Prove2me | Theorems.Thm_NagaevLD_GenMoment_convexity_step
-- name    : NagaevLD.GenMoment.convexity_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:25.392267+00:00
-- url     : https://prove2.me/theorems/816f42e9-3865-4387-af03-55b821ecff74
-- title:
--   Convexity step, p. 767 — g′(x/n)x/n ≥ g(x/n) − g(0), hence e^{hx/n−g(x/n)} ≥ e^{−g(0)} for h = g′(x/n)
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ have, on $[0,\infty)$, a positive nondecreasing derivative $g'$. Let $n\ge 1$ be an integer, $x>0$, and $h=g'(x/n)$. Then
--   $$g'(x/n)\,\frac{x}{n}\ \ge\ g(x/n)-g(0),$$
--   and consequently
--   $$e^{hx/n-g(x/n)}\ \ge\ e^{-g(0)} .$$
--
--   The first inequality expresses the convexity of $g$ (its graph lies above the tangent line at $x/n$, evaluated at $0$). The second is the form used to prove (2.48), which in turn lets the negative part of $Ee^{hX_j}$ be absorbed into the factor $e^{hx/n-g(x/n)}$.
--
--   **Formalization Note** The paper prints the first inequality with a strict "$>$". It fails when $g'$ is constant on $[0,x/n]$ — for example $g(u)=Tu$, a case the paper itself discusses on p. 768 — so the non-strict inequality is stated; the proof of Theorem 2.5 only uses the second inequality, which the paper prints with "$\ge$". The hypotheses on $g$ are imposed on $[0,\infty)$ only. The implicit $n\ge1$ of the paper is explicit in Lean.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 767, proof of Theorem 2.5, between (2.47) and (2.48)

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Convexity step of the proof of Theorem 2.5, p. 767: `g′(x/n)·x/n ≥ g(x/n) − g(0)` and,
for `h = g′(x/n)`, `e^{hx/n − g(x/n)} ≥ e^{−g(0)}`. (The page prints a strict `>` in the first
inequality; it fails when `g′` is constant on `[0, x/n]`, so the non-strict form is stated.) -/
theorem convexity_step (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    g (x / n) - g 0 ≤ g' (x / n) * (x / n) ∧
      Real.exp (-g 0) ≤ Real.exp (h * (x / n) - g (x / n)) := by sorry

end NagaevLD.GenMoment
