-- Prove2me | Theorems.Thm_GlobalTheory_InertCompletion_continuous_of_valued_eq
-- name    : GlobalTheory.InertCompletion.continuous_of_valued_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:18:33.804239+00:00
-- url     : https://prove2.me/theorems/8351669b-594f-4c98-9fdf-30be85011458
-- title:
--   Inert Completion: continuous of valued eq
-- statement:
--   The Inert Completion construction uses the continuous of valued eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRingEquivTensorInertAdicCompletion.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRingEquivTensorInertAdicCompletion.lean#L51-L55

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
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

theorem GlobalTheory.InertCompletion.continuous_of_valued_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (σ : P.adicCompletion E →+* P.adicCompletion E) (h : ∀ x, Valued.v (σ x) = Valued.v x) :
    Continuous σ := by sorry
