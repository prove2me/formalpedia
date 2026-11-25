-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sUnits_sup_locNorm_ne_top
-- name    : GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:46:48.494253+00:00
-- url     : https://prove2.me/theorems/49206c52-e0fd-41cc-a68a-f9349234823a
-- title:
--   QNorm: s Units sup loc Norm ne top
-- statement:
--   The QNorm construction uses the s Units sup loc Norm ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsSupUnitsLocalNormsSqrtNeTop.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitsSupUnitsLocalNormsSqrtNeTop.lean#L26-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
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

theorem GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by sorry
