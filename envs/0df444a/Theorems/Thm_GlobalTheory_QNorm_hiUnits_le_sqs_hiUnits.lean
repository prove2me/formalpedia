-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_hiUnits_le_sqs_hiUnits
-- name    : GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.935101+00:00
-- url     : https://prove2.me/theorems/2e2fd96a-bd90-448d-89c0-da51e29a6116
-- title:
--   QNorm: hi Units le sqs hi Units
-- statement:
--   The QNorm construction uses the hi Units le sqs hi Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HigherUnitsLeSquaresHigherUnits.lean#L27-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HigherUnitsLeSquaresHigherUnits.lean#L27-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
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
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by sorry
