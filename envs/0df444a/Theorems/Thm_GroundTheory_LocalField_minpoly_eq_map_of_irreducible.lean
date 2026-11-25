-- Prove2me | Theorems.Thm_GroundTheory_LocalField_minpoly_eq_map_of_irreducible
-- name    : GroundTheory.LocalField.minpoly_eq_map_of_irreducible
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:35.40695+00:00
-- url     : https://prove2.me/theorems/c31fc7c0-747f-5c84-a603-73bb103aeceb
-- title:
--   Local Field: minpoly eq map of irreducible
-- statement:
--   The Local Field construction uses the minpoly eq map of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L501-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L501-L503

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

theorem GroundTheory.LocalField.minpoly_eq_map_of_irreducible :
    minpoly K (ϖ : L) = (minpoly 𝒪[K] (ϖ : L)).map (algebraMap 𝒪[K] K) := by sorry
