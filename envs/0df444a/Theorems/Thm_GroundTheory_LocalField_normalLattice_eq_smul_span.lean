-- Prove2me | Theorems.Thm_GroundTheory_LocalField_normalLattice_eq_smul_span
-- name    : GroundTheory.LocalField.normalLattice_eq_smul_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:06.387217+00:00
-- url     : https://prove2.me/theorems/f7e86251-c8be-58d4-af89-d52ac01dbc30
-- title:
--   Local Field: normal Lattice eq smul span
-- statement:
--   The Local Field construction uses the normal Lattice eq smul span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L432-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L432-L434

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open scoped Pointwise

theorem GroundTheory.LocalField.normalLattice_eq_smul_span (π : 𝒪[K]) (θ : L) (s : ℕ) :
    normalLattice π θ s = π ^ s • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ) := by sorry
