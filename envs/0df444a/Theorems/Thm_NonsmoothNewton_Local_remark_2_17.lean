-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_remark_2_17
-- name    : NonsmoothNewton.Local.remark_2_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:03:16.353867+00:00
-- url     : https://prove2.me/theorems/e97a296c-6d7e-43a9-80be-ee417f3a8777
-- title:
--   Remark (2.17) — first-order expansion $F(x+h)-F(x)-F'(x;h)=o(\|h\|)$ at a semismooth point
-- statement:
--   Let $E$, $G$ be finite-dimensional real normed spaces, $F : E \to G$ locally Lipschitz, and $x \in E$.
--
--   1. If $F$ is semismooth at $x$, then as $h \to 0$
--   $$
--   F(x+h) - F(x) - F'(x;h) = o(\|h\|). \tag{2.17}
--   $$
--   2. If $0 < p \le 1$ and $F$ is $p$-order semismooth at $x$, then as $h \to 0$
--   $$
--   F(x+h) - F(x) - F'(x;h) = O(\|h\|^{1+p}).
--   $$
--
--   Together with (2.8), the expansion (2.17) is what lets the Newton step be compared with the directional derivative at the root in the proof of Theorem 3.2; the second clause gives the order $1+p$.
--
--   **Formalization Note** The $o(\|h\|)$ is pinned as: for every $\varepsilon > 0$ there is $\delta > 0$ with $\|F(x+h)-F(x)-F'(x;h)\| \le \varepsilon\|h\|$ whenever $\|h\| < \delta$. The $O(\|h\|^{1+p})$ is pinned as: there are $C$ and $\delta > 0$ with the same norm $\le C\|h\|^{1+p}$ whenever $\|h\| < \delta$. The Remark is unnumbered in the paper and cited by its equation number.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 358, Section 2, Remark, Eq. (2.17)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Section 2, Remark, Eq. (2.17), p. 358. For locally Lipschitz `F`:
if `F` is semismooth at `x` then `F(x + h) - F(x) - F'(x; h) = o(‖h‖)`; if `F` is
`p`-order semismooth at `x` (`0 < p ≤ 1`) then `F(x + h) - F(x) - F'(x; h) = O(‖h‖^{1+p})`. -/
theorem remark_2_17 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    (SemismoothAt F x → ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
        ‖F (x + h) - F x - dirDeriv F x h‖ ≤ ε * ‖h‖) ∧
    (∀ p : ℝ, 0 < p → p ≤ 1 → POrderSemismoothAt p F x →
      ∃ C δ : ℝ, 0 < δ ∧ ∀ h : E, ‖h‖ < δ →
        ‖F (x + h) - F x - dirDeriv F x h‖ ≤ C * ‖h‖ ^ (1 + p)) := by sorry

end NonsmoothNewton.Local
