-- Prove2me | Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mem_relBrauer_iff
-- name    : GroundTheory.Brauer.BrauerGroup.mk_mem_relBrauer_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:10.777718+00:00
-- url     : https://prove2.me/theorems/2279fd50-7df6-4592-adb2-fda40bf87211
-- title:
--   Brauer Group: mk mem rel Brauer iff
-- statement:
--   The Brauer Group construction uses the mk mem rel Brauer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L75-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L75-L94

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
variable {K L}

theorem GroundTheory.Brauer.BrauerGroup.mk_mem_relBrauer_iff (A : CSA.{u, u} K) :
    ⟦A⟧ ∈ relBrauer K L ↔
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by sorry
