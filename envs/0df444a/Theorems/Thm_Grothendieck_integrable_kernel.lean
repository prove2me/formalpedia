-- Prove2me | Theorems.Thm_Grothendieck_integrable_kernel
-- name    : Grothendieck.integrable_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:47:20.793471+00:00
-- url     : https://prove2.me/theorems/88c0a7bf-8657-4a30-9853-56d4af0de1dd
-- title:
--   The Laplace kernel of Lemma 2.1 is integrable on the plane
-- statement:
--   For $r\ge2$ and $|\tau|<1$, the Laplace kernel
--   $$(s,t)\mapsto (st)^{-1/2}\Big((1+2s)(1+2t)-4\tau^2st\Big)^{-\frac{r+2}{2}}$$
--   is integrable for the product of Lebesgue measure restricted to the positive quadrant.
--
--   This is what lets the two-parameter integral of Lemma 2.1 be iterated, and hence what lets the substitutions $s=u^2/2$, $t=v^2/2$ be applied one variable at a time.
--
--   The proof is a comparison. Expanding,
--   $$(1+2s)(1+2t)-4\tau^2st=(1-\tau^2)(1+2s)(1+2t)+\tau^2(1+2s+2t)\ \ge\ (1-\tau^2)(1+2s)(1+2t),$$
--   and since the exponent $-\frac{r+2}{2}$ is negative the kernel is bounded in absolute value by $(1-\tau^2)^{-\frac{r+2}{2}}$ times $g(s)g(t)$ with $g(u)=u^{-1/2}(1+2u)^{-\frac{r+2}{2}}$. That $g$ is integrable on $(0,\infty)$: on $(0,1]$ it is at most $u^{-1/2}$, and on $(1,\infty)$ at most $u^{-\frac{r+3}{2}}$, whose exponent exceeds $1$ for $r\ge2$.
--
--   **Formalization Note** Supporting lemma for Lemma 2.1; the one-dimensional companion is `Grothendieck.integrableOn_one_dim`.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, the two-parameter integral of its proof.

import Mathlib
import Definitions.Def_Grothendieck_Fubini

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The Laplace kernel is integrable on the plane.** For `r ≥ 2` and `|τ| < 1`,
`(s,t) ↦ (st)^{-1/2}((1+2s)(1+2t)-4τ²st)^{-(r+2)/2}` is integrable for `planeMeasure`. -/
theorem integrable_kernel (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      planeMeasure := by sorry

end Grothendieck
