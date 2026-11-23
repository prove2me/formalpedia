-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_proposition_7
-- name    : LogBarrierIPM.Iterations.Supplement.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:13:53.518173+00:00
-- url     : https://prove2.me/theorems/22193a85-b01f-40bb-a92c-4f257147f688
-- title:
--   Proposition 7 — valuation of an orthant polyhedron
-- statement:
--   Let $d\ge1$ and $\mathcal P=\{x\in K^d:Ax\le b\}\subseteq K_+^d$. Then
--   $$\operatorname{val}(\mathcal P)\text{ is a tropical polyhedron in }\mathbb T^d.$$
--   The conclusion supplies a finite system of tropical affine inequalities for the valuation image. Empty polyhedra and zero coordinates are included. This identifies the target set in Theorem 9.
--
--   Differences from the source:
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: 1-based finite vectors and the tropical semiring → 0-based Fin vectors and WithBot real coordinates; reason: the index shift preserves every coordinate, including bottom values
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 10, Proposition 7

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem proposition_7 {p d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (Fin p) (Fin d) Puiseux) (b : Fin p → Puiseux)
    (horthant : kOrthant (kPolyhedron A b)) :
    IsTropicalPolyhedron (valVec '' kPolyhedron A b) := by sorry

end LogBarrierIPM.Iterations.Supplement
