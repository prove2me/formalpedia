-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_exists_congr_iff_trace_forms_isometric
-- name    : GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:01.154826+00:00
-- url     : https://prove2.me/theorems/ea4375c0-dc54-4e63-bf84-4ad6230da89d
-- title:
--   Local Quad: exists congr iff trace forms isometric
-- statement:
--   The Local Quad construction uses the exists congr iff trace forms isometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L169-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L169-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix

theorem GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h2 : (2 : E) ≠ 0) (c : E →+* E) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {n : Type*} [Fintype n] [DecidableEq n] {G G' : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (hG' : ∀ a b, c (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
      ∃ φ : (n → E) ≃ₗ[F] (n → E),
        ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x) := by sorry
