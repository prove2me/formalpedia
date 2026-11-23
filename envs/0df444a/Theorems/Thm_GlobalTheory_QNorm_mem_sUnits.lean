-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
-- name    : GlobalTheory.QNorm.mem_sUnits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:39.575854+00:00
-- url     : https://prove2.me/theorems/3a5a6fbe-6ac3-4b60-a916-ff1b6cc915c7
-- title:
--   QNorm: mem s Units
-- statement:
--   The QNorm construction uses the mem s Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L74-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.QNorm.mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ sUnits F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (x : F) = 1 := by sorry
