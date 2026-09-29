-- Prove2me | Theorems.Thm_OPG434_clebsch16_equivalence
-- name    : OPG434.clebsch16_equivalence
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T05:04:48.755373+00:00
-- url     : https://prove2.me/theorems/db904c48-90a5-4102-836a-5a3176ff5a3f
-- title:
--   Weak-pentagon colorings and the sixteen-vertex target
-- statement:
--   For every finite simple graph $G$, a weak-pentagon five-edge labeling exists exactly when $G$ has a homomorphism to the graph on four-bit vectors whose adjacent labels have Hamming distance three or four:
--
--   $$
--   G\text{ has a weak-pentagon coloring}
--   \quad\Longleftrightarrow\quad
--   G\longrightarrow H_{16}.
--   $$
--
--   Both sides are existential. The conversion is not required to preserve an arbitrary previously chosen edge labeling or vertex map.
-- source:
--   Open Problem Garden weak pentagon reformulations; explicit candidate normalization at commit bc0d53de15bb21236483b4d671dda376309c8177, research/artifacts/candidates/opg434-a01-c02-normalization.md

import Definitions.Def_opg434_weak_pentagon

namespace OPG434

universe u

/-- Existence of a weak-pentagon coloring is equivalent to a homomorphism to
the explicit sixteen-vertex Hamming-distance target. -/
theorem clebsch16_equivalence
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    HasWeakPentagonColoring G ↔ HasClebsch16Homomorphism G := by sorry

end OPG434
