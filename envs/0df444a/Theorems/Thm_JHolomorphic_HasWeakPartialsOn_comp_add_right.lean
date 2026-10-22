-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_comp_add_right
-- name    : JHolomorphic.HasWeakPartialsOn.comp_add_right
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T15:57:49.120994+00:00
-- url     : https://prove2.me/theorems/13e695d4-12d2-4722-9dd7-2aea975bd3d3
-- title:
--   Weak partial derivatives commute with translation
-- statement:
--   Let $E$ be a real normed space, $U\subseteq\mathbb{C}$, and let $f_s,f_t$ be weak partial derivatives of $f:\mathbb{C}\to E$ on $U$. Then for every $a\in\mathbb{C}$ the translates $f_s(\cdot+a)$ and $f_t(\cdot+a)$ are weak partial derivatives of $f(\cdot+a)$ on the translated set
--   $$U-a=\{z\in\mathbb{C}: z+a\in U\}.$$
--   This is the basic compatibility of weak derivatives with translations, used for difference quotients.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; the first weak partial is the derivative in the direction $1$ and the second in the direction $i$. The translated set is the preimage `(· + a) ⁻¹' U`.
-- source:
--   Standard (weak derivatives and Lebesgue spaces).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- If `fₛ`, `fₜ` are weak partial derivatives of `f` on `U`, then `fₛ(· + a)`, `fₜ(· + a)` are
weak partial derivatives of `f(· + a)` on the translated set `U - a`. -/
theorem HasWeakPartialsOn.comp_add_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f fs ft : ℂ → E} (h : HasWeakPartialsOn U f fs ft) (a : ℂ) :
    HasWeakPartialsOn ((· + a) ⁻¹' U) (fun z => f (z + a)) (fun z => fs (z + a))
      (fun z => ft (z + a)) := by
  sorry

end JHolomorphic
