-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Nakayama_valuation_natCast_lt_one
-- name    : GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:27.033751+00:00
-- url     : https://prove2.me/theorems/df7910c6-e973-468e-ac24-19c56cc78c1d
-- title:
--   Nakayama: valuation nat Cast lt one
-- statement:
--   The Nakayama construction uses the valuation nat Cast lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L61-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Nakayama
variable (F : Type) [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : (N : 𝓞 F) ∈ v.asIdeal) :
    Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by sorry
