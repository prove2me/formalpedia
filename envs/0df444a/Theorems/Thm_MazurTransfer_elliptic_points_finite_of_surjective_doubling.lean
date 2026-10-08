-- Prove2me | Theorems.Thm_MazurTransfer_elliptic_points_finite_of_surjective_doubling
-- name    : MazurTransfer.elliptic_points_finite_of_surjective_doubling
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T17:10:56.611411+00:00
-- url     : https://prove2.me/theorems/473f6cf4-ef20-4126-a77c-6e80479d3dd8
-- title:
--   Surjective doubling forces finiteness of elliptic points under Northcott
-- statement:
--   Let $F$ be a field with an admissible system of absolute values whose logarithmic affine height has the Northcott property, and let $E/F$ be an elliptic curve. If doubling is surjective on its point group, then
--   \[2E(F)=E(F)\quad\Longrightarrow\quad E(F)\text{ is finite}.\]
--   Height descent first gives finite generation. The index formula for multiplication by two then forces the free rank to vanish. The named downstream consumer is the exact order-18 descent: its arithmetic calculation proves the doubling hypothesis rather than assuming it in the final torsion exclusion.
-- source:
--   Height descent and the finitely generated group index formula from user MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Original Michael Stoll provenance (EllipticCurves commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f), Apache-2.0 headers, and authors retained. The finiteness deduction generalizes the original X1(18) rank-zero consumer without changing its downstream statement.

import Mathlib

theorem MazurTransfer.elliptic_points_finite_of_surjective_doubling :
∀ (F : Type*) [Field F] [DecidableEq F]
    [Height.AdmissibleAbsValues F] [Northcott (Height.logHeight₁ (K := F))]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic],
    (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range = ⊤ →
      Finite W.toAffine.Point := by sorry
