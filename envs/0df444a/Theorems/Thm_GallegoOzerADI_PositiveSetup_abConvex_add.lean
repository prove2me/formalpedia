-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_abConvex_add
-- name    : GallegoOzerADI.PositiveSetup.abConvex_add
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:46:54.784626+00:00
-- url     : https://prove2.me/theorems/21199e21-67ae-43e7-8a4d-c8131e34361a
-- title:
--   Lemma 1, Part 2 — $\alpha f + \beta g \in C(\alpha a + \beta a', \alpha b + \beta b')$
-- statement:
--   Let $a, b, a', b' \ge 0$, let $f \in C(a,b)$ and $g \in C(a',b')$, and let $\alpha > 0$ and $\beta > 0$. Then
--
--   $$
--   \alpha f + \beta g \in C(\alpha a + \beta a',\ \alpha b + \beta b').
--   $$
--
--   Positive combinations of $(a,b)$-convex functions stay in the class, with the allowances combined linearly. In the proof of Theorem 1 this is how the single-period cost $G_{n-1}$ (convex, so in $C(0,0)$) and the discounted expected cost-to-go combine into $V_{n-1}$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1349, Lemma 1, Part 2

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_add (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (f g : ℝ → ℝ) (hf : ABConvex a b f) (hg : ABConvex a' b' g) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) :
    ABConvex (α * a + β * a') (α * b + β * b') (fun x => α * f x + β * g x) := by sorry

end GallegoOzerADI.PositiveSetup
