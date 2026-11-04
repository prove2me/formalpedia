-- Prove2me | Theorems.Thm_Grothendieck_integrable_kernel_subst
-- name    : Grothendieck.integrable_kernel_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:51:00.572767+00:00
-- url     : https://prove2.me/theorems/20701441-8f18-42d9-bea9-4100a02d88fd
-- title:
--   The substituted kernel of Lemma 2.1 is integrable on the plane
-- statement:
--   For $r\ge2$ and $|\tau|<1$, the **substituted kernel**
--   $$(u,v)\mapsto\Big((1+u^2)(1+v^2)-\tau^2u^2v^2\Big)^{-\frac{r+2}{2}}$$
--   is integrable for the product of Lebesgue measure restricted to the positive quadrant.
--
--   This is the integrability that lets the two-parameter integral of Lemma 2.1 be iterated *after* the substitutions $s=u^2/2$, $t=v^2/2$ have removed the singular factor — which is what the final assembly of the matrix Grothendieck identity needs.
--
--   The estimate: writing $a=u^2$, $b=v^2$, $\sigma=\tau^2$,
--   $$(1+a)(1+b)-\sigma ab=(1-\sigma)(1+a)(1+b)+\sigma(1+a+b)\ \ge\ (1-\sigma)(1+a)(1+b)>0,$$
--   so since the exponent is negative the kernel is at most $(1-\sigma)^{-\frac{r+2}{2}}(1+u^2)^{-\frac{r+2}{2}}(1+v^2)^{-\frac{r+2}{2}}$, a product of a constant with an integrable function of $u$ and one of $v$ — and $(1+x^2)^{-M}$ is integrable on $(0,\infty)$ for $M>\frac12$.
--
--   **Formalization Note** Companion of `Grothendieck.integrable_kernel` (the unsubstituted kernel); this is the form the iterated argument uses.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, after the substitutions s=u^2/2, t=v^2/2.

import Mathlib
import Definitions.Def_Grothendieck_Fubini

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The substituted kernel is integrable on the plane.** For `r ≥ 2` and `|τ| < 1`,
`(u,v) ↦ ((1+u²)(1+v²)-τ²u²v²)^{-(r+2)/2}` is integrable for `planeMeasure`. -/
theorem integrable_kernel_subst (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by sorry

end Grothendieck
