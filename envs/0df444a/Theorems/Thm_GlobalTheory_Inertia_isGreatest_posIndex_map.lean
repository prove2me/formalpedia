-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex_map
-- name    : GlobalTheory.Inertia.isGreatest_posIndex_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:12.913868+00:00
-- url     : https://prove2.me/theorems/30b7098f-4708-54b0-a8a4-53bb3b0a0a89
-- title:
--   Inertia: is Greatest pos Index map
-- statement:
--   The Inertia construction uses the is Greatest pos Index map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L448-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L448-L452

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

theorem GlobalTheory.Inertia.isGreatest_posIndex_map (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → 0 < (FD.hermC τ G x x).re} (posIndex (G.map τ)) := by sorry
