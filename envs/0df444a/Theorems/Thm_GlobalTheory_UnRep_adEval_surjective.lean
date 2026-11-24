-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_adEval_surjective
-- name    : GlobalTheory.UnRep.adEval_surjective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:07.806529+00:00
-- url     : https://prove2.me/theorems/0caf4881-9d75-4c73-a3b2-1cd026185ac4
-- title:
--   Un Rep: ad Eval surjective
-- statement:
--   The Un Rep construction uses the ad Eval surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L79-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
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

theorem GlobalTheory.UnRep.adEval_surjective (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (adEval F v) := by sorry
