-- Prove2me | Theorems.Thm_NelderMeadLD_Conv1D_lemma_4_1
-- name    : NelderMeadLD.Conv1D.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:50.104979+00:00
-- url     : https://prove2.me/theorems/85050ec9-8de6-40e6-a5b0-0eb3c4905dd8
-- title:
--   Lemma 4.1, pp. 124–125 — strictly convex f on ℝ: up–down–up brackets x_min; f increases beyond x_min; f continuous
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be strictly convex, and let $x_{\min}$ be a minimizer of $f$ (necessarily unique). For reals $a, b$ write $\operatorname{int}(a, b)$ for the open interval with endpoints $a$ and $b$ and $\operatorname{int}[a, b]$ for the closed one, whichever endpoint is larger.
--
--   1. If $y_1, y_2, y_3$ are three distinct points with $y_2 \in \operatorname{int}(y_1, y_3)$, then
--   $$f(y_1) \ge f(y_2)\ \text{ and }\ f(y_2) \le f(y_3) \implies x_{\min} \in \operatorname{int}(y_1, y_3).$$
--   2. If $y_1 \ne y_2$ and $x_{\min} \in \operatorname{int}[y_1, y_2]$, then for all $\xi_2 > \xi_1 \ge 1$,
--   $$f\big(y_2 + \xi_2(y_1 - y_2)\big) > f\big(y_2 + \xi_1(y_1 - y_2)\big).$$
--   3. $f$ is continuous.
--
--   The first part says that an "up–down–up" pattern of values brackets the minimizer; the second that $f$ strictly increases along the ray leaving the minimizer's side of $y_1$. Both are used repeatedly in the one-dimensional analysis of the Nelder–Mead method.
--
--   **Formalization Note** Part 2 adds $y_1 \ne y_2$: at $y_1 = y_2$ both points coincide and the strict inequality fails; the page's $\operatorname{int}[y_1, y_2]$ presupposes two endpoints. The page's lemma does not use bounded level sets, and none is assumed; the minimizer is a hypothesis, as in the lemma.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), pp. 124–125, Lemma 4.1

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_1 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y) :
    (∀ y1 y2 y3 : ℝ, y1 ≠ y2 → y2 ≠ y3 → y1 ≠ y3 →
        min y1 y3 < y2 → y2 < max y1 y3 → f y2 ≤ f y1 → f y2 ≤ f y3 →
        min y1 y3 < xmin ∧ xmin < max y1 y3) ∧
    (∀ y1 y2 : ℝ, y1 ≠ y2 → xmin ∈ Set.uIcc y1 y2 →
        ∀ ξ1 ξ2 : ℝ, 1 ≤ ξ1 → ξ1 < ξ2 →
          f (y2 + ξ1 * (y1 - y2)) < f (y2 + ξ2 * (y1 - y2))) ∧
    Continuous f := by sorry

end NelderMeadLD.Conv1D
