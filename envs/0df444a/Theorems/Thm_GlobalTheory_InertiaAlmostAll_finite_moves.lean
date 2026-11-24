-- Prove2me | Theorems.Thm_GlobalTheory_InertiaAlmostAll_finite_moves
-- name    : GlobalTheory.InertiaAlmostAll.finite_moves
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:16.267469+00:00
-- url     : https://prove2.me/theorems/ed9b21b2-223b-4349-bfd4-e6f4e18bb727
-- title:
--   Inertia Almost All: finite moves
-- statement:
--   The Inertia Almost All construction uses the finite moves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L30-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L30-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll

theorem GlobalTheory.InertiaAlmostAll.finite_moves (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (x : Ω) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ τ ∈ Ine (F := F) B, τ x ≠ x}.Finite := by sorry
