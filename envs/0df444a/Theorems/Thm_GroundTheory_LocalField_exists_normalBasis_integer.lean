-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_normalBasis_integer
-- name    : GroundTheory.LocalField.exists_normalBasis_integer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:20.458556+00:00
-- url     : https://prove2.me/theorems/1b2a709c-3800-465f-b55e-a71377d3765d
-- title:
--   Local Field: exists normal Basis integer
-- statement:
--   The Local Field construction uses the exists normal Basis integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L374-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L374-L392

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
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
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K L]

theorem GroundTheory.LocalField.exists_normalBasis_integer {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ θ : L, (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧ ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L] := by sorry
