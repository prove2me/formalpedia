-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_cor_2_5
-- name    : NonsmoothNewton.Local.cor_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:04:58.933211+00:00
-- url     : https://prove2.me/theorems/33da3ab9-f217-4890-91f8-50c7554a9122
-- title:
--   Corollary 2.5 — a strong Fréchet derivative implies semismoothness
-- statement:
--   Let $E$, $G$ be finite-dimensional real normed spaces, $F : E \to G$ locally Lipschitz, and $x \in E$. Suppose $F$ has a **strong Fréchet derivative** $F'(x)$ at $x$, i.e.
--
--   $$
--   \lim_{\substack{y \to x \\ z \to x}} \frac{F(z) - F(y) - F'(x)(z-y)}{\|z-y\|} = 0 .
--   $$
--
--   Then $F$ is semismooth at $x$.
--
--   This shows that the class of semismooth maps contains every map that is strictly differentiable at the point, in particular every continuously differentiable map.
--
--   **Formalization Note** The paper's display (2.16) prints $F(x)$ in the numerator where $F(z)$ is meant; as printed the limit fails for every nonconstant $F$. The proof of the corollary (taking $z = y + th$) and the cited definition of Ortega–Rheinboldt use $F(z)$, and the corrected form is stated. It is Mathlib's `HasStrictFDerivAt`, which reads the quotient as $\|F(z)-F(y)-F'(x)(z-y)\| = o(\|z-y\|)$ as $(y,z) \to (x,x)$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 358, Corollary 2.5 (definition (2.16), same page)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Corollary 2.5, p. 358. If the locally Lipschitz map `F` has a strong
Fréchet derivative `F'` at `x` (Mathlib's `HasStrictFDerivAt`: the corrected (2.16),
`(F z - F y - F'(z - y)) / ‖z - y‖ → 0` as `y, z → x`), then `F` is semismooth at `x`. -/
theorem cor_2_5 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) (F' : E →L[ℝ] G)
    (hstrong : HasStrictFDerivAt F F' x) :
    SemismoothAt F x := by sorry

end NonsmoothNewton.Local
