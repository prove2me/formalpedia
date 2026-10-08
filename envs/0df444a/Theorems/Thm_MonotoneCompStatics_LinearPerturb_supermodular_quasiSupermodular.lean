-- Prove2me | Theorems.Thm_MonotoneCompStatics_LinearPerturb_supermodular_quasiSupermodular
-- name    : MonotoneCompStatics.LinearPerturb.supermodular_quasiSupermodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:07.816843+00:00
-- url     : https://prove2.me/theorems/a5ff5a43-7658-4fcc-9d78-14a06bd7448e
-- title:
--   p. 164 remark — every supermodular function is quasisupermodular
-- statement:
--   Let $X$ be a lattice and $g : X \to \mathbb{R}$ be **supermodular**, i.e.
--
--   $$
--   g(x) + g(y) \le g(x \vee y) + g(x \wedge y) \qquad \text{for all } x, y \in X.
--   $$
--
--   Then $g$ is **quasisupermodular**: for all $x, y \in X$, $g(x) \ge g(x \wedge y)$ implies $g(x \vee y) \ge g(y)$, and $g(x) > g(x \wedge y)$ implies $g(x \vee y) > g(y)$.
--
--   This is the first half of the remark following Theorem 5 in Milgrom and Shannon. It places the cardinal theory of Topkis inside the ordinal theory of the paper, and it is the step of Theorem 10 that turns supermodularity of $f(x,t) + p\cdot x$ into quasisupermodularity in $x$.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 164 (PDF p. 9), remark after Theorem 5

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 164, remark after Theorem 5: every supermodular function on a
lattice is quasisupermodular. -/
theorem supermodular_quasiSupermodular {X : Type*} [Lattice X] (g : X → ℝ)
    (hg : Supermodularity.Monotonicity.SupermodularOn g Set.univ) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn g Set.univ := by sorry

end MonotoneCompStatics.LinearPerturb
