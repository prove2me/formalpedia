-- Prove2me | Theorems.Thm_GlobalTheory_sesq_rules_of_combination
-- name    : GlobalTheory.sesq_rules_of_combination
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:30.041134+00:00
-- url     : https://prove2.me/theorems/fe190b3b-0f32-4d20-abe5-134ce03a2ed7
-- title:
--   Global Theory: sesq rules of combination
-- statement:
--   The Global Theory construction uses the sesq rules of combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RieszEigenvectorSesquilinearFunctionSpace.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RieszEigenvectorSesquilinearFunctionSpace.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RieszEigenvectorSesquilinearFunctionSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory

theorem GlobalTheory.sesq_rules_of_combination {X : Type} (C : Submodule ℂ (X → ℂ)) (F : (X → ℂ) → (X → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → F (a • f + f') g = star a * F f g + F f' g)
    (hr : ∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → F f (a • g + g') = a * F f g + F f g') :
    (∀ f f' g, f ∈ C → f' ∈ C → g ∈ C → F (f + f') g = F f g + F f' g) ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F (a • f) g = star a * F f g) ∧
    (∀ f g g', f ∈ C → g ∈ C → g' ∈ C → F f (g + g') = F f g + F f g') ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F f (a • g) = a * F f g) := by sorry
