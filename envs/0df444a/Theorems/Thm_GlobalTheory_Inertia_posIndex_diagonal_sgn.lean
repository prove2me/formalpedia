-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_posIndex_diagonal_sgn
-- name    : GlobalTheory.Inertia.posIndex_diagonal_sgn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:14.82008+00:00
-- url     : https://prove2.me/theorems/4859d29c-6b47-4c87-8a19-153858357857
-- title:
--   Inertia: pos Index diagonal sgn
-- statement:
--   The Inertia construction uses the pos Index diagonal sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L365-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L365-L368

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {r s : ℕ}

theorem GlobalTheory.Inertia.posIndex_diagonal_sgn {p : ℕ} (hp : p ≤ r) :
    posIndex (diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) = p := by sorry
