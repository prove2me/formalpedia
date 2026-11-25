-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_comparison_injective
-- name    : GroundTheory.PAdicHodge.IsRegular.comparison_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:21.595295+00:00
-- url     : https://prove2.me/theorems/cacd9290-f59c-4cf1-8c26-15805cff5b00
-- title:
--   Is Regular: comparison injective
-- statement:
--   The Is Regular construction uses the comparison injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L226-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L226-L239

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

theorem GroundTheory.PAdicHodge.IsRegular.comparison_injective [FiniteDimensional F V] : Function.Injective (comparison B ρ) := by sorry
