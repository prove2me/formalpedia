-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_places_inertia_not_fixing_finiteExtension
-- name    : GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:43.882911+00:00
-- url     : https://prove2.me/theorems/8b4dc1ef-4df0-40d1-b702-284a9845414e
-- title:
--   T: finite places inertia not fixing finite Extension
-- statement:
--   The T construction uses the finite places inertia not fixing finite Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtensionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtensionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by sorry
