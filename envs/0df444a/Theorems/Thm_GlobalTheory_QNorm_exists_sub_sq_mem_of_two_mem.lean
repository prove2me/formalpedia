-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_sub_sq_mem_of_two_mem
-- name    : GlobalTheory.QNorm.exists_sub_sq_mem_of_two_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:36.29324+00:00
-- url     : https://prove2.me/theorems/237b8723-3b7d-4ea4-b32e-e6e1afa358c5
-- title:
--   QNorm: exists sub sq mem of two mem
-- statement:
--   The QNorm construction uses the exists sub sq mem of two mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSubSqLtOneOfTwoLtOne.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSubSqLtOneOfTwoLtOne.lean#L9-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.exists_sub_sq_mem_of_two_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (a : 𝓞 F) :
    ∃ b : 𝓞 F, a - b ^ 2 ∈ v.asIdeal := by sorry
