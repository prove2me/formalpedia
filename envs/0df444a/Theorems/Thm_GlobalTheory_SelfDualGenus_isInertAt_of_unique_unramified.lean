-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_isInertAt_of_unique_unramified
-- name    : GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:53:30.915414+00:00
-- url     : https://prove2.me/theorems/0714de72-820a-4c58-9d89-ef967785f9b1
-- title:
--   Self Dual Genus: is Inert At of unique unramified
-- statement:
--   The Self Dual Genus construction uses the is Inert At of unique unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsInertAtOfUniqueUnramifiedPrime.lean#L13-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsInertAtOfUniqueUnramifiedPrime.lean#L13-L74

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrime
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
open GlobalTheory GlobalTheory.SelfDualGenus
open IsDedekindDomain NumberField
open scoped TensorProduct Matrix

theorem GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ _root_.GlobalTheory.SelfDualGenus.semiLoc v))
    (hx : ∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E,
      (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧
        y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) :
    _root_.Formalism.UG.IsInertAt (maximalRealSubfield E) E v P := by sorry
