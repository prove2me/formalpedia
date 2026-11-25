-- Prove2me | Theorems.Thm_GlobalTheory_HL_TraceConjugationCover_stMat_spec
-- name    : GlobalTheory.HL.TraceConjugationCover.stMat_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:45.05908+00:00
-- url     : https://prove2.me/theorems/48c3bf0e-3559-411e-ab24-129ab3cfe8e5
-- title:
--   Trace Conjugation Cover: st Mat spec
-- statement:
--   The Trace Conjugation Cover construction uses the st Mat spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StMatSpec.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StMatSpec.lean#L17-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StMatSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.HL
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceConjugationCover
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem GlobalTheory.HL.TraceConjugationCover.stMat_spec (G : GFrames A r k) (x : G.GLV)
    (h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) :
    ∀ b, x (G.f' b) = ∑ a, stMat G x a b • G.f' a := by sorry
