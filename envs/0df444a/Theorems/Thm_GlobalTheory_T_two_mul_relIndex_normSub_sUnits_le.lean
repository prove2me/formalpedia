-- Prove2me | Theorems.Thm_GlobalTheory_T_two_mul_relIndex_normSub_sUnits_le
-- name    : GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:39.34619+00:00
-- url     : https://prove2.me/theorems/7857b03e-709e-483a-b8ba-e8b0cea0c61f
-- title:
--   T: two mul rel Index norm Sub s Units le
-- statement:
--   The T construction uses the two mul rel Index norm Sub s Units le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FirstInequalitySUnitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FirstInequalitySUnitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ 2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ 2 ^ (tFin F δ S + tReal F δ) := by sorry
