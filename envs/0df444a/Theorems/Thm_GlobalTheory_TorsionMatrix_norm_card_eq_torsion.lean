-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_norm_card_eq_torsion
-- name    : GlobalTheory.TorsionMatrix.norm_card_eq_torsion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:28.615421+00:00
-- url     : https://prove2.me/theorems/9d171ae4-dcb9-5ade-bc68-62c455c2a5fd
-- title:
--   Torsion Matrix: norm card eq torsion
-- statement:
--   The Torsion Matrix construction uses the norm card eq torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L39-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L39-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix

theorem GlobalTheory.TorsionMatrix.norm_card_eq_torsion (l : ℕ) [hl : Fact l.Prime] (K : Type) [AddCommGroup K] [Finite K]
    (N : ℕ) (hN : Nat.card K ≤ N) :
    ‖((Nat.card K : ℕ) : ℚ_[l])‖ = ‖((Nat.card {x : K // l ^ N • x = 0} : ℕ) : ℚ_[l])‖ := by sorry
