-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_finrank_le
-- name    : GroundTheory.PAdicHodge.IsRegular.finrank_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:51.185606+00:00
-- url     : https://prove2.me/theorems/2b4fd971-f717-49f6-9234-0cd6872ea842
-- title:
--   Is Regular: finrank le
-- statement:
--   The Is Regular construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L222-L224

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
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
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

theorem GroundTheory.PAdicHodge.IsRegular.finrank_le [FiniteDimensional F V] :
    finrank (invariantRing G F B) (DB B ρ) ≤ finrank F V := by sorry
