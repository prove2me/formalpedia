-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_eq_zero_of_forall_dotProduct_eq_zero
-- name    : GlobalTheory.HermWitt.eq_zero_of_forall_dotProduct_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:40.554957+00:00
-- url     : https://prove2.me/theorems/43ca6b04-8775-4f29-a0c3-11b2103ca9c4
-- title:
--   Herm Witt: eq zero of forall dot Product eq zero
-- statement:
--   The Herm Witt construction uses the eq zero of forall dot Product eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L291-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L291-L298

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.HermWitt.eq_zero_of_forall_dotProduct_eq_zero {G : Matrix n n E} (hG : G.det ≠ 0) {x : n → E}
    (hx : ∀ y, y ⬝ᵥ G *ᵥ (c ∘ x) = 0) : x = 0 := by sorry
