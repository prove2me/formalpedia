-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Conv_exists_generator
-- name    : GlobalTheory.CMVal.Conv.exists_generator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:29.323228+00:00
-- url     : https://prove2.me/theorems/fff718ad-5643-4e4c-8ed2-2eb1d6e59154
-- title:
--   Conv: exists generator
-- statement:
--   The Conv construction uses the exists generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntegersOfMemHatO.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntegersOfMemHatO.lean#L44-L49

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.CMVal.Conv.exists_generator : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by sorry
