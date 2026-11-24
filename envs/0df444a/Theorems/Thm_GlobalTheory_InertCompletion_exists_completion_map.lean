-- Prove2me | Theorems.Thm_GlobalTheory_InertCompletion_exists_completion_map
-- name    : GlobalTheory.InertCompletion.exists_completion_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:18:24.050184+00:00
-- url     : https://prove2.me/theorems/4c0bd8f6-affd-4199-8be7-39bba6fbe342
-- title:
--   Inert Completion: exists completion map
-- statement:
--   The Inert Completion construction uses the exists completion map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRingEquivTensorInertAdicCompletion.lean#L14-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRingEquivTensorInertAdicCompletion.lean#L14-L49

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.InertCompletion
open scoped WithZeroTopology

theorem GlobalTheory.InertCompletion.exists_completion_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : IsInertAt F E v P) :
    ∃ φ : v.adicCompletion F →+* P.adicCompletion E, Continuous φ ∧
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (φ x) = Valued.v x := by sorry
