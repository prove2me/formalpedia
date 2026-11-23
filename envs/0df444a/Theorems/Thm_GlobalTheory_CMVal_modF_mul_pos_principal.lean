-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_modF_mul_pos_principal
-- name    : GlobalTheory.CMVal.modF_mul_pos_principal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:29.0678+00:00
-- url     : https://prove2.me/theorems/b0ceafc0-4863-4185-8b87-60daf275cb15
-- title:
--   CMVal: mod F mul pos principal
-- statement:
--   The CMVal construction uses the mod F mul pos principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L55-L56

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem GlobalTheory.CMVal.modF_mul_pos_principal : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ := by sorry
