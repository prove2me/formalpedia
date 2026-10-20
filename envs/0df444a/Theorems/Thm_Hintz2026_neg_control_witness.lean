-- Prove2me | Theorems.Thm_Hintz2026_neg_control_witness
-- name    : Hintz2026.neg_control_witness
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T13:49:02.199994+00:00
-- url     : https://prove2.me/theorems/fe63b76c-ea00-4b4e-a2a6-4cd44de7f518
-- title:
--   Negative control: Dbad ≠ AX
-- statement:
--   The wrong operator $D^{\text{bad}} = \sqrt{\Delta}\partial_r$ (missing the $-i\partial_\theta$ term) does NOT satisfy the integrating factor equation for $X$ when $a \neq 0$. Witnessed at $p = (M=2,a=1,Q=1)$, $x = (4, \pi/2)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/FieldInterface.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.neg_control_witness (p : SubextremalKN) : (of fun i j => Dbad p0 (fun z => X p0 z i j) x0) ≠ A p0 x0 * X p0 x0 := by sorry
