-- Prove2me | Theorems.Thm_GroundTheory_LocalField_pow_smul_mem_normalLattice
-- name    : GroundTheory.LocalField.pow_smul_mem_normalLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:59.999675+00:00
-- url     : https://prove2.me/theorems/7de447ac-141d-453d-ae62-e4c3f61eeb49
-- title:
--   Local Field: pow smul mem normal Lattice
-- statement:
--   The Local Field construction uses the pow smul mem normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L75-L79

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

theorem GroundTheory.LocalField.pow_smul_mem_normalLattice {t u : ℕ} {x : L} (hx : x ∈ normalLattice π θ t) :
    π ^ u • x ∈ normalLattice π θ (t + u) := by sorry
