-- Prove2me | Theorems.Thm_GeomDL_Blueprint_act_linear
-- name    : GeomDL.Blueprint.act_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:15.478597+00:00
-- url     : https://prove2.me/theorems/d5f5a4fc-098a-4521-8d4e-9c72c8baeb66
-- title:
--   §3.1, pp. 14–15 — the action on signals is linear, g.(αx + βx′) = α(g.x) + β(g.x′)
-- statement:
--   Let a group $\mathfrak G$ act on a domain $\Omega$, and let $\mathfrak G$ act on real signals $x : \Omega \to \mathbb R$ by $(\mathfrak g . x)(u) = x(\mathfrak g^{-1} u)$. Then the action is linear: for every $\mathfrak g \in \mathfrak G$, all scalars $\alpha, \beta \in \mathbb R$ and all signals $x, x'$,
--   $$\mathfrak g . (\alpha x + \beta x') = \alpha (\mathfrak g . x) + \beta (\mathfrak g . x') .$$
--
--   Linearity is what makes the action on signals a group representation.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.1, display at the top of p. 15 (sentence begins on p. 14)

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.1, pp. 14–15: the action (3) on real signals is linear, in the sense that
`g.(αx + βx′) = α(g.x) + β(g.x′)` for any scalars `α, β` and signals `x, x′`. -/
theorem act_linear {G Ω : Type*} [Group G] [MulAction G Ω]
    (g : G) (α β : ℝ) (x x' : Ω → ℝ) :
    act g (α • x + β • x') = α • act g x + β • act g x' := by sorry

end GeomDL.Blueprint
