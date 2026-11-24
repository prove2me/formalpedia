-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_valuation_eq_one_of_norm_one_of_not_moved
-- name    : GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:51.382818+00:00
-- url     : https://prove2.me/theorems/4027daa2-63f4-4ad8-b44c-73f004ef309a
-- title:
--   Un Rep: valuation eq one of norm one of not moved
-- statement:
--   The Un Rep construction uses the valuation eq one of norm one of not moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationEqOneOfNormOneOfNotMoved.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationEqOneOfNormOneOfNotMoved.lean#L24-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by sorry
