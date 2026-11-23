-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_le_card_of_mem_posDims
-- name    : GlobalTheory.Inertia.le_card_of_mem_posDims
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:35.382311+00:00
-- url     : https://prove2.me/theorems/0a0b28a3-f1c8-427c-b5a8-947e6c32729c
-- title:
--   Inertia: le card of mem pos Dims
-- statement:
--   The Inertia construction uses the le card of mem pos Dims property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L25-L28

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
variable {n m : Type*} [Fintype n] [Fintype m]

theorem GlobalTheory.Inertia.le_card_of_mem_posDims {G : Matrix n n ℂ} {d : ℕ} (hd : d ∈ posDims G) :
    d ≤ Fintype.card n := by sorry
