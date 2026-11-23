-- Prove2me | Theorems.Thm_GroundTheory_LocalField_normalLattice_antitone
-- name    : GroundTheory.LocalField.normalLattice_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:32.126251+00:00
-- url     : https://prove2.me/theorems/cdc93976-ac4d-4b4c-8936-eef13c762b2d
-- title:
--   Local Field: normal Lattice antitone
-- statement:
--   The Local Field construction uses the normal Lattice antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L69-L73

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
variable (π : 𝒪[K]) (θ : L)
omit [FiniteDimensional K L]

theorem GroundTheory.LocalField.normalLattice_antitone : Antitone (normalLattice π θ) := by sorry
