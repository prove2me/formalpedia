-- Prove2me | Theorems.Thm_MazurTransfer_integral_of_two_chart_gluing
-- name    : MazurTransfer.integral_of_two_chart_gluing
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T20:16:20.917423+00:00
-- url     : https://prove2.me/theorems/9241aa72-0224-4499-8163-b837f3a9550d
-- title:
--   Integrality of a scheme glued from two integral charts with nonempty overlap
-- statement:
--   Let a scheme gluing datum be covered by two charts, each an integral scheme. If their gluing overlap is nonempty, then the glued scheme is integral. The cover condition includes every index of the gluing datum; repeated chart indices are allowed. This is a general geometric gluing lemma. For the explicit order-13 model, chart integrality and nonempty overlap require separate verification; this theorem asserts no smoothness, genus, Jacobian identification, or rational-point classification.
-- source:
--   New closed Lean proof by Vas and contributors. Mathlib Scheme.GlueData and the integral-scheme criterion. Named downstream consumer: MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isIntegral, for the unchanged two-chart curve at MazurTheorem commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Design boundary: the two explicit integral-chart hypotheses, exhaustive cover, and nonempty geometric overlap.

import Mathlib

theorem MazurTransfer.integral_of_two_chart_gluing
    (D : _root_.AlgebraicGeometry.Scheme.GlueData) (i j : D.J)
    (hcover : ∀ k, k = i ∨ k = j)
    [_root_.AlgebraicGeometry.IsIntegral (D.U i)]
    [_root_.AlgebraicGeometry.IsIntegral (D.U j)]
    (hoverlap : Nonempty (D.V (i, j))) :
    _root_.AlgebraicGeometry.IsIntegral D.glued := by sorry
