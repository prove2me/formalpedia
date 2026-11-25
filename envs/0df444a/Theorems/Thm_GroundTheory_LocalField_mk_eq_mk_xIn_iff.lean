-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mk_eq_mk_xIn_iff
-- name    : GroundTheory.LocalField.mk_eq_mk_xIn_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:54.159937+00:00
-- url     : https://prove2.me/theorems/ca2e9332-9d1a-41c4-9070-09b16ce5493b
-- title:
--   Local Field: mk eq mk x In iff
-- statement:
--   The Local Field construction uses the mk eq mk x In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L148-L152

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
omit [Fintype G] hp

theorem GroundTheory.LocalField.mk_eq_mk_xIn_iff (h : elemSub p x) :
    (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) ↔
      x⁻¹ * (h : G) ∈ sylowCent p x := by sorry
