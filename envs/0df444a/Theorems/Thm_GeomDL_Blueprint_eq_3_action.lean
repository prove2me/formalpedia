-- Prove2me | Theorems.Thm_GeomDL_Blueprint_eq_3_action
-- name    : GeomDL.Blueprint.eq_3_action
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:22.206985+00:00
-- url     : https://prove2.me/theorems/bb7c3f60-c811-4582-98d7-fb4c27efefea
-- title:
--   §3.1, (3), p. 14 — (g.x)(u) = x(g⁻¹u) is a group action on signals: g.(h.x) = (gh).x
-- statement:
--   Let a group $\mathfrak G$ act on a domain $\Omega$, and let $\mathfrak G$ act on signals $x : \Omega \to C$ by equation (3), $(\mathfrak g . x)(u) = x(\mathfrak g^{-1} u)$. Then this is a (left) group action on signals: for all $\mathfrak g, \mathfrak h \in \mathfrak G$ and every signal $x$,
--   $$\mathfrak g . (\mathfrak h . x) = (\mathfrak g \mathfrak h) . x, \qquad 1 . x = x .$$
--
--   The inverse in (3) is what makes the induced map compose in the right order; it is the basis of every equivariance statement in the book.
--
--   **Formalization Note** The book states the composition law; the unit law $1 . x = x$ is added so that the conclusion is the full definition of an action.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.1, equation (3) and the sentence after it, p. 14

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.1, p. 14, after equation (3): "Due to the inverse on g, this is indeed a
valid group action, in that we have (g.(h.x))(u) = ((gh).x)(u)." Together with the unit law,
`act` is a (left) action of `G` on signals `x : Ω → C`. -/
theorem eq_3_action {G Ω C : Type*} [Group G] [MulAction G Ω] :
    (∀ (g h : G) (x : Ω → C), act g (act h x) = act (g * h) x) ∧
    (∀ x : Ω → C, act (1 : G) x = x) := by sorry

end GeomDL.Blueprint
