-- Prove2me | Theorems.Thm_GlobalTheory_HermDiag_coe_complexConj_ringHom
-- name    : GlobalTheory.HermDiag.coe_complexConj_ringHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:08.238246+00:00
-- url     : https://prove2.me/theorems/52fcc63e-c04e-4d5b-a188-6eec283e4a5d
-- title:
--   Herm Diag: coe complex Conj ring Hom
-- statement:
--   The Herm Diag construction uses the coe complex Conj ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L246-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean#L246-L247

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.HermDiag.coe_complexConj_ringHom :
    ⇑((IsCMField.complexConj E : E →+* E)) = FD.cc := by sorry
