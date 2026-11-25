-- Prove2me | Theorems.Thm_GlobalTheory_T_riesz_eigenvector_sesquilinear_function_space
-- name    : GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:32.4598+00:00
-- url     : https://prove2.me/theorems/bab39cf7-bbf8-48ef-9148-8d04d73fb8a9
-- title:
--   T: riesz eigenvector sesquilinear function space
-- statement:
--   The T construction uses the riesz eigenvector sesquilinear function space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RieszEigenvectorSesquilinearFunctionSpaceStatement.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RieszEigenvectorSesquilinearFunctionSpaceStatement.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RieszEigenvectorSesquilinearFunctionSpace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RieszEigenvectorSesquilinearFunctionSpaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by sorry
