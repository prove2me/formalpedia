-- Prove2me | Theorems.Thm_MazurTransfer_x0_27_map_certificate_1
-- name    : MazurTransfer.x0_27_map_certificate_1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:09:42.956977+00:00
-- url     : https://prove2.me/theorems/a147ed7e-e980-4b2a-999e-df7c4e4ac927
-- title:
--   X0(27) rational-map polynomial certificate 1
-- statement:
--   For rational $s_1,s_2,s_3$ satisfying the indicated consecutive $X_0(9)$ correspondence equation, the displayed cleared-denominator polynomial expression reduces to the specified remainder (certificate 1) or the remainder vanishes (certificate 2). All coefficient functions are the fixed polynomials of the imported map data. These two identities establish that the rational map lands on $y^2+y=x^3-7$ wherever its denominators are nonzero. The downstream consumer separately handles every vanishing-denominator case and classifies the chained correspondence; neither certificate asserts a rational-root existence claim.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.NumberTheory.XZeroTwentySevenClassification, curve_key_step₁. Complete original quantified signature and proof body retained via Lean AST byte ranges.

import Mathlib
import Definitions.Def_MazurTransfer_XZeroTwentySevenMapCertificateData

open MazurTorsion.XZeroTwentySeven

theorem MazurTransfer.x0_27_map_certificate_1 {s₁ s₂ s₃ : ℚ}
    (h1 : s₁ ^ 2 * s₂ ^ 3 + 36 * s₁ ^ 2 * s₂ ^ 2 + 270 * s₁ ^ 2 * s₂ - s₁ ^ 3 +
      729 * s₁ * s₂ ^ 2 + 26244 * s₁ * s₂ + 531441 * s₂ = 0) :
    (mapNya s₂ s₃ ^ 2 + mapNya s₂ s₃ * mapDya s₂ s₃ + 7 * mapDya s₂ s₃ ^ 2) *
        mapDx s₁ s₂ s₃ ^ 3 - mapNx s₁ s₂ s₃ ^ 3 * mapDya s₂ s₃ ^ 2 =
      remPart0 s₁ s₂ s₃ + remPart1 s₁ s₂ s₃ + remPart2 s₁ s₂ s₃ + remPart3 s₁ s₂ s₃
        + remPart4 s₁ s₂ s₃ + remPart5 s₁ s₂ s₃ + remPart6 s₁ s₂ s₃ + remPart7 s₁ s₂ s₃
        + remPart8 s₁ s₂ s₃ + remPart9 s₁ s₂ s₃ + remPart10 s₁ s₂ s₃ + remPart11 s₁ s₂ s₃
        + remPart12 s₁ s₂ s₃ + remPart13 s₁ s₂ s₃ + remPart14 s₁ s₂ s₃ + remPart15 s₁ s₂ s₃
        + remPart16 s₁ s₂ s₃ + remPart17 s₂ s₃ + remPart18 s₂ s₃ + remPart19 s₂ s₃
        + remPart20 s₂ s₃ + remPart21 s₂ s₃ + remPart22 s₂ s₃ + remPart23 s₂ s₃
        + remPart24 s₂ s₃  := by sorry
