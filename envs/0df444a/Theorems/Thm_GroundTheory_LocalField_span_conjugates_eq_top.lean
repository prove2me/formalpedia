-- Prove2me | Theorems.Thm_GroundTheory_LocalField_span_conjugates_eq_top
-- name    : GroundTheory.LocalField.span_conjugates_eq_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:41.876817+00:00
-- url     : https://prove2.me/theorems/488445a0-317d-4b08-bc2b-a272fdea92dc
-- title:
--   Local Field: span conjugates eq top
-- statement:
--   The Local Field construction uses the span conjugates eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L439-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L439-L443

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

theorem GroundTheory.LocalField.span_conjugates_eq_top {θ : L} (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ := by sorry
