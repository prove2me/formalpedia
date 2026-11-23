-- Prove2me | Theorems.Thm_GlobalTheory_shortComplex_quasiIso_iff
-- name    : GlobalTheory.shortComplex_quasiIso_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:18.645588+00:00
-- url     : https://prove2.me/theorems/6fce4643-2303-44e7-a93e-a4bb468fde27
-- title:
--   Global Theory: short Complex quasi Iso iff
-- statement:
--   The Global Theory construction uses the short Complex quasi Iso iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L350-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L350-L394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]

theorem GlobalTheory.shortComplex_quasiIso_iff {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 → ∃ (x : S.X₂) (z : T.X₁), S.g x = 0 ∧ T.f z + φ.τ₂ x = y) ∧
      (∀ (x : S.X₂) (z : T.X₁), S.g x = 0 → T.f z = φ.τ₂ x → ∃ w : S.X₁, S.f w = x) := by sorry
