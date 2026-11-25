-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_sylowCent_iff
-- name    : GroundTheory.LocalField.mem_sylowCent_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:23.795233+00:00
-- url     : https://prove2.me/theorems/6cb4a53d-8574-4d55-a107-9f3e7a12d90e
-- title:
--   Local Field: mem sylow Cent iff
-- statement:
--   The Local Field construction uses the mem sylow Cent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L203-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L203-L229

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
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
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit [Fintype G]

theorem GroundTheory.LocalField.mem_sylowCent_iff (hx : (orderOf x).Coprime p) {z : G} (hz : (orderOf z).Coprime p) :
    x⁻¹ * z ∈ sylowCent p x ↔ z = x := by sorry
