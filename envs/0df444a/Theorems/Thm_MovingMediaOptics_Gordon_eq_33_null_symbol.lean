-- Prove2me | Theorems.Thm_MovingMediaOptics_Gordon_eq_33_null_symbol
-- name    : MovingMediaOptics.Gordon.eq_33_null_symbol
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:22.985562+00:00
-- url     : https://prove2.me/theorems/503f924f-918b-4047-98de-abd82f890c46
-- title:
--   (30)–(33), pp. 4–5 — Gordon's null symbol is the ray dispersion polynomial
-- statement:
--   In a nondispersive dielectric, let $c>0$ be the vacuum light speed, $n\geq1$ the refractive index, $u\in\mathbb R^3$ the medium velocity with $|u|<c$, $k\in\mathbb R^3$ a spatial wave vector, and $\omega\in\mathbb R$ a laboratory frequency. Set $\gamma=(1-|u|^2/c^2)^{-1/2}$ and use the covariant wave vector $k_\nu=(\omega/c,-k)$. Gordon's contravariant metric is $g^{\mu\nu}=\eta^{\mu\nu}+(n^2-1)U^\mu U^\nu$, where $U=\gamma(1,u/c)$ and $\eta=\operatorname{diag}(1,-1,-1,-1)$. Then
--
--   $$c^2g^{\mu\nu}k_\mu k_\nu=\omega^2-c^2|k|^2+(n^2-1)\gamma^2(\omega-u\cdot k)^2.$$
--
--   Thus the eikonal null condition (30) is precisely the dispersion relation (33). This identifies the geometric and Hamiltonian descriptions of a wave covector.
--
--   **Formalization Note** The index range is $0,1,2,3$, with coordinate zero equal to $ct$. The $n\geq1$ and subluminal-flow assumptions record the paper's regime; the algebraic identity uses only $c\ne0$.
-- source:
--   Leonhardt & Piwnicki, Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, pp. 4–5, §III.B, (29)–(33)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace MovingMediaOptics.Gordon

/-- Leonhardt–Piwnicki, arXiv:physics/9906038v3, pp. 4–5, (29)–(33). -/
theorem eq_33_null_symbol (c n : ℝ) (u k : V3) (omega : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    c ^ 2 * quadratic (gUp c n u) (waveCovector c omega k) =
      rayDispersion c n u k omega := by sorry

end MovingMediaOptics.Gordon
