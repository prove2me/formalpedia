-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_compound_mul
-- name    : GroundTheory.PAdicHodge.compound_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:18.925811+00:00
-- url     : https://prove2.me/theorems/ffb974c2-14d6-42a1-ac06-264cedb697b1
-- title:
--   PAdic Hodge: compound mul
-- statement:
--   The PAdic Hodge construction uses the compound mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L149-L156

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

theorem GroundTheory.PAdicHodge.compound_mul {l : ℕ} (P : Matrix (Fin m) (Fin n) R) (Q : Matrix (Fin n) (Fin l) R) :
    compound k (P * Q) = compound k P * compound k Q := by sorry
