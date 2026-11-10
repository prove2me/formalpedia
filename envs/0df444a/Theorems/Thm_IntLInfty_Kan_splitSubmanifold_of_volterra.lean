-- Prove2me | Theorems.Thm_IntLInfty_Kan_splitSubmanifold_of_volterra
-- name    : IntLInfty.Kan.splitSubmanifold_of_volterra
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:20.150321+00:00
-- url     : https://prove2.me/theorems/4a8d2700-06c8-4483-b765-821d2e109dcd
-- title:
--   Level sets of a Volterra chart are split submanifolds
-- statement:
--   Let $E$ be Banach, $G:E\to E$ smooth, $H$ a continuous linear idempotent, $M=\{z: H(z-G z)=0\}$, and suppose $\|(DG_x)^n\|<1$ for some $n$ at every $x\in M$. Then $$M\ \text{is a}\ C^\infty\ \text{split submanifold of}\ E.$$
--
--   Role: the inverse-function-theorem step of K0b, over abstract data.
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem splitSubmanifold_of_volterra {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (G : E → E) (hG : ContDiff ℝ ∞ G) (H : E →L[ℝ] E) (hH : ∀ z, H (H z) = H z)
    (M : Set E) (hM : ∀ z, z ∈ M ↔ H (z - G z) = 0)
    (hV : ∀ x ∈ M, ∃ n : ℕ, ‖(fderiv ℝ G x) ^ n‖ < 1) : IsSplitSubmanifold M := by sorry

end IntLInfty.Kan
