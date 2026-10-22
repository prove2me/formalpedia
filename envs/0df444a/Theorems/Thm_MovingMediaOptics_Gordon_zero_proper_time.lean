-- Prove2me | Theorems.Thm_MovingMediaOptics_Gordon_zero_proper_time
-- name    : MovingMediaOptics.Gordon.zero_proper_time
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:12.337033+00:00
-- url     : https://prove2.me/theorems/ba86c1bb-d1c6-488c-bfd7-f5b34e856524
-- title:
--   §III.D, p. 6 — the ray tangent has zero Gordon proper time
-- statement:
--   Let $c>0$ be the vacuum light speed, $n\geq1$ the refractive index, and $u\in\mathbb R^3$ a subluminal medium velocity. For a nonzero spatial wave vector $k$, let $H(k)$ be the positive comoving-frequency Hamiltonian (34), and let $v=\nabla_k H(k)$ be the laboratory ray velocity. The laboratory tangent in coordinates $x^0=ct$ is $(c,v)$. Then
--
--   $$g_{\mu\nu}(c,v)^\mu(c,v)^\nu=0,$$
--
--   where $g_{\mu\nu}=\eta_{\mu\nu}+(n^{-2}-1)U_\mu U_\nu$ is Gordon's covariant metric. This gives the pointwise null part of the ray-geodesic claim in §III.D.
--
--   **Formalization Note** The wave vector is nonzero because the gradient of the square-root Hamiltonian is not the ray direction at $k=0$. No condition $H(k)>0$ is imposed: the chosen branch has positive comoving frequency, while its laboratory frequency may be negative.
-- source:
--   Leonhardt & Piwnicki, Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, p. 6, §III.D, sentence after (51): 'the proper time is zero on the ray trajectory'

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace MovingMediaOptics.Gordon

/-- Leonhardt–Piwnicki, arXiv:physics/9906038v3, p. 6, §III.D, after (51). -/
theorem zero_proper_time (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    quadratic (gDown c n u)
      ![c, rayVelocity c n u k 0, rayVelocity c n u k 1, rayVelocity c n u k 2] = 0 := by sorry

end MovingMediaOptics.Gordon
