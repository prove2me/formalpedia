-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_theorem_2_3
-- name    : NonsmoothNewton.Local.theorem_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:02:41.814461+00:00
-- url     : https://prove2.me/theorems/a2fa2f6f-a6ab-41a8-8cfc-a62833fc6906
-- title:
--   Theorem 2.3 (i)⇔(iv)⇔(v) — characterizations of semismoothness
-- statement:
--   Let $E$, $G$ be finite-dimensional real normed spaces, $F : E \to G$ locally Lipschitz, and $x \in E$. Write $D_F$ for the set of points where $F$ is differentiable. The following statements are equivalent:
--
--   1. (i) $F$ is semismooth at $x$;
--   2. (iv) $F'(x;h)$ exists for every $h$, and for $V \in \partial F(x+h)$, $h \to 0$,
--   $$
--   Vh - F'(x;h) = o(\|h\|); \tag{2.8}
--   $$
--   3. (v) $F'(x;h)$ exists for every $h$, and
--   $$
--   \lim_{\substack{x+h\in D_F \\ h\to 0}} \frac{F'(x+h;h) - F'(x;h)}{\|h\|} = 0. \tag{2.9}
--   $$
--
--   Condition (2.8) is the form of semismoothness used in the local convergence proof of the nonsmooth Newton method (Theorem 3.2), and (2.9) is the form used to check semismoothness of concrete maps.
--
--   **Formalization Note** The statement is the conjunction of (i) ⇔ (iv) and (i) ⇔ (v); the paper's parts (ii) and (iii) (uniform convergence of the limits in (2.7) and (2.5) over unit directions) are not included. Both $o(\cdot)$ statements are pinned to their $\varepsilon$–$\delta$ content: for every $\varepsilon > 0$ there is $\delta > 0$ such that $\|Vh - F'(x;h)\| \le \varepsilon\|h\|$ for all $\|h\| < \delta$ and $V \in \partial F(x+h)$, respectively $\|JF(x+h)h - F'(x;h)\| \le \varepsilon \|h\|$ for all $\|h\| < \delta$ with $x + h \in D_F$. At a point of differentiability $F'(x+h;h)$ equals $JF(x+h)h$, which is how (v) is written. Existence of $F'(x;\cdot)$, which (2.8) and (2.9) presuppose, is part of conditions (iv) and (v).
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 356, Theorem 2.3 (i), (iv), (v); Eqs. (2.8), (2.9)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Theorem 2.3, p. 356, parts (i) ⇔ (iv) ⇔ (v). For locally Lipschitz `F`:
(i) `F` is semismooth at `x`;
(iv) `F'(x; ·)` exists and `V h - F'(x; h) = o(‖h‖)` for `V ∈ ∂F(x + h)`, `h → 0` (2.8);
(v) `F'(x; ·)` exists and `(F'(x + h; h) - F'(x; h)) / ‖h‖ → 0` as `h → 0` with
`x + h ∈ D_F` (2.9), where at a point of differentiability `F'(x + h; h) = JF(x + h) h`. -/
theorem theorem_2_3 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    (SemismoothAt F x ↔
      ((∀ h : E, ∃ d : G, HasDirDerivAt F x h d) ∧
        ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ → ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + h),
          ‖V h - dirDeriv F x h‖ ≤ ε * ‖h‖)) ∧
    (SemismoothAt F x ↔
      ((∀ h : E, ∃ d : G, HasDirDerivAt F x h d) ∧
        ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ → DifferentiableAt ℝ F (x + h) →
          ‖fderiv ℝ F (x + h) h - dirDeriv F x h‖ ≤ ε * ‖h‖)) := by sorry

end NonsmoothNewton.Local
