-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algEquiv_algebraMap_integer
-- name    : GroundTheory.LocalField.algEquiv_algebraMap_integer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:09.025105+00:00
-- url     : https://prove2.me/theorems/2b50f4c9-5375-44a5-9b33-2d6cbea2331c
-- title:
--   Local Field: alg Equiv algebra Map integer
-- statement:
--   The Local Field construction uses the alg Equiv algebra Map integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L256-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L256-L258

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
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L]

theorem GroundTheory.LocalField.algEquiv_algebraMap_integer (τ : Gal(L/K)) (c : 𝒪[K]) :
    τ (algebraMap 𝒪[K] L c) = algebraMap 𝒪[K] L c := by sorry
