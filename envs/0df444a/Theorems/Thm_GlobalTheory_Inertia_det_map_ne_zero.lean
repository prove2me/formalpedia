-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_det_map_ne_zero
-- name    : GlobalTheory.Inertia.det_map_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:56.609929+00:00
-- url     : https://prove2.me/theorems/12aa5975-776e-4cbb-a166-53a65f6153c5
-- title:
--   Inertia: det map ne zero
-- statement:
--   The Inertia construction uses the det map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L426-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L426-L430

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
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.Inertia.det_map_ne_zero {n : Type*} [Fintype n] [DecidableEq n] (τ : E →+* ℂ) {G : Matrix n n E}
    (hG0 : G.det ≠ 0) : (G.map τ).det ≠ 0 := by sorry
