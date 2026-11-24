-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_admissible_localNorm_mem_sUnits_sup_globalNorm
-- name    : GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:59.434812+00:00
-- url     : https://prove2.me/theorems/154fdf98-87aa-47b6-9c0e-1f18f5b0867d
-- title:
--   T: exists admissible local Norm mem s Units sup global Norm
-- statement:
--   The T construction uses the exists admissible local Norm mem s Units sup global Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) → ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ, (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) → t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by sorry
