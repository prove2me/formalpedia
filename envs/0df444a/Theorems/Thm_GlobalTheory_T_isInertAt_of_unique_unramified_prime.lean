-- Prove2me | Theorems.Thm_GlobalTheory_T_isInertAt_of_unique_unramified_prime
-- name    : GlobalTheory.T.isInertAt_of_unique_unramified_prime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:08.854699+00:00
-- url     : https://prove2.me/theorems/034a1243-7c6f-52e2-aa1c-475f73379969
-- title:
--   T: is Inert At of unique unramified prime
-- statement:
--   The T construction uses the is Inert At of unique unramified prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsInertAtOfUniqueUnramifiedPrimeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsInertAtOfUniqueUnramifiedPrimeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrime
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrimeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isInertAt_of_unique_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ semiLoc v)) → (∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E, (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInertAt (maximalRealSubfield E) E v P := by sorry
