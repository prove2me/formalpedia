-- Prove2me | Theorems.Thm_GlobalTheory_InertiaLift_exists_mem_Ine_lift
-- name    : GlobalTheory.InertiaLift.exists_mem_Ine_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:17.311496+00:00
-- url     : https://prove2.me/theorems/4b38f281-28c2-4449-8358-e7d9c4a684a9
-- title:
--   Inertia Lift: exists mem Ine lift
-- statement:
--   The Inertia Lift construction uses the exists mem Ine lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L120-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteGaloisInertiaLiftsAbsoluteInertiaRat.lean#L120-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem GlobalTheory.InertiaLift.exists_mem_Ine_lift (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω]
    [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 → A.valuation ((algebraMap M Ω (τ x)) - (algebraMap M Ω x)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := by sorry
