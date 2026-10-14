-- Prove2me | Theorems.Thm_KerrBL_vacKerr_rr
-- name    : KerrBL.vacKerr_rr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:33:35.242847+00:00
-- url     : https://prove2.me/theorems/998de469-4803-4ee3-818b-e5c7d6556df3
-- title:
--   Explicit Kerr Ricci component $R_{rr}$ vanishes as a rational identity
-- statement:
--   Let $M,a,r,s,c,S,D$ be real numbers subject to
--
--   $$s^2+c^2=1,\qquad S=r^2+a^2c^2,\qquad D=a^2+r^2-2Mr,\qquad S\neq0,\quad D\neq0,\quad s\neq0 .$$
--
--   Then the explicit closed-form Ricci component of the Boyer-Lindquist Kerr metric (definition `RicciKerr` of `KerrBL_Kerr_ClosedForms`) vanishes:
--
--   $$\mathrm{RicciKerr}_{rr}(M,a;\,r,s,c,S,D)=0 .$$
--
--   This is a pure identity of rational functions in seven real variables: $s$ and $c$ need not be a sine and a cosine, and $S,D$ need not be evaluated from $r,c$; the trigonometric relation enters only through the hypothesis $s^2+c^2=1$ and the atoms only through the two side equations. Layer III of the mission consists of this identity for each of the eight components that are not structurally zero; `ricci_flat_Kerr` instantiates them at a point of the regular domain via `ricci_bridge_Kerr`.
--
--   **Formalization Note** The non-vanishing hypotheses are exactly the denominators that occur in the closed forms. No assumption about curvature is made: `RicciKerr` is the full Ricci formula with the generated closed forms substituted, and the statement asserts that this expression reduces to $0$.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N16 (vacKerr_rr)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.vacKerr_rr (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    RicciKerr M a 1 1 r s c S D = 0 := by sorry
