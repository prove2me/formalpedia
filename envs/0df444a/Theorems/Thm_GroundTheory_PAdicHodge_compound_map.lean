-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_compound_map
-- name    : GroundTheory.PAdicHodge.compound_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:26.402876+00:00
-- url     : https://prove2.me/theorems/db738e6a-51e5-4320-a022-08b8b8871c70
-- title:
--   PAdic Hodge: compound map
-- statement:
--   The PAdic Hodge construction uses the compound map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L164-L168

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
variable {R : Type*} [CommRing R]
variable {m n k : ℕ}

theorem GroundTheory.PAdicHodge.compound_map {S : Type*} [CommRing S] (f : R →+* S) (P : Matrix (Fin m) (Fin n) R) :
    compound k (P.map f) = (compound k P).map f := by sorry
