-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_compound_apply
-- name    : GroundTheory.PAdicHodge.compound_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:49.365617+00:00
-- url     : https://prove2.me/theorems/b8b7c4b1-ab19-441d-aa8d-e456ab8763c4
-- title:
--   PAdic Hodge: compound apply
-- statement:
--   The PAdic Hodge construction uses the compound apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L125-L126

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

theorem GroundTheory.PAdicHodge.compound_apply (k : ℕ) (P : Matrix (Fin m) (Fin n) R) (s : KSubset m k)
    (t : KSubset n k) : compound k P s t = (P.submatrix s.emb t.emb).det := by sorry
