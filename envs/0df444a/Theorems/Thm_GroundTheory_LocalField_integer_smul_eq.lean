-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integer_smul_eq
-- name    : GroundTheory.LocalField.integer_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:03.760799+00:00
-- url     : https://prove2.me/theorems/d503ebce-a26b-4058-9741-2f0549a67bf4
-- title:
--   Local Field: integer smul eq
-- statement:
--   The Local Field construction uses the integer smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L13-L15

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

theorem GroundTheory.LocalField.integer_smul_eq (c : 𝒪[K]) (y : L) : c • y = algebraMap K L (c : K) * y := by sorry
