-- Prove2me | Theorems.Thm_MovingMediaOptics_Gordon_eq_51_rest_frame_metric
-- name    : MovingMediaOptics.Gordon.eq_51_rest_frame_metric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:15.69692+00:00
-- url     : https://prove2.me/theorems/b0856d43-5a42-4eb8-afdf-8adef202c3e5
-- title:
--   (50)–(51), p. 6 — Gordon's line element in the local rest frame
-- statement:
--   Let $c>0$, $n\geq1$, and let $u\in\mathbb R^3$ be a medium velocity with $|u|<c$. Write $\Lambda(u)$ for the Lorentz boost taking a displacement $v=(c\,dt',dx'_1,dx'_2,dx'_3)$ from the local rest frame to the laboratory frame. Gordon's covariant metric is $g_{\mu\nu}=\eta_{\mu\nu}+(n^{-2}-1)U_\mu U_\nu$, with $U=\gamma(1,u/c)$ and $\eta=\operatorname{diag}(1,-1,-1,-1)$. For every rest-frame displacement $v$,
--
--   $$g_{\mu\nu}(\Lambda v)^\mu(\Lambda v)^\nu=\frac{v_0^2}{n^2}-(v_1^2+v_2^2+v_3^2).$$
--
--   This is the local-rest-frame line element (51), $ds^2=c^2dt'^2/n^2-|dx'|^2$. It exposes the light cone of the optical metric at one event.
--
--   **Formalization Note** The published boost is the identity at $u=0$. The subluminal condition makes its Lorentz factor physical; $n\geq1$ records the paper's regime but is not needed for the algebraic identity. This statement is also the pointwise second conjunct of the existing Open goal.
-- source:
--   Leonhardt & Piwnicki, Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, p. 6, §III.D, (50)–(51)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace MovingMediaOptics.Gordon

/-- Leonhardt–Piwnicki, arXiv:physics/9906038v3, p. 6, (50)–(51). -/
theorem eq_51_rest_frame_metric (c n : ℝ) (u : V3) (v : V4)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    quadratic (gDown c n u) (apply4 (lorentzBoost c u) v) =
      (v 0) ^ 2 / n ^ 2 - ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by sorry

end MovingMediaOptics.Gordon
