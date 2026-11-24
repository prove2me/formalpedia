-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_card_filter_sgn_pos
-- name    : GlobalTheory.Inertia.card_filter_sgn_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:31.742883+00:00
-- url     : https://prove2.me/theorems/b89f72a8-4649-41bc-a95f-4bb494b8f0c0
-- title:
--   Inertia: card filter sgn pos
-- statement:
--   The Inertia construction uses the card filter sgn pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L360-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L360-L363

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

theorem GlobalTheory.Inertia.card_filter_sgn_pos {p : ℕ} (hp : p ≤ r) :
    (Finset.univ.filter fun a : Fin r => 0 < FD.sgn p a).card = p := by sorry
