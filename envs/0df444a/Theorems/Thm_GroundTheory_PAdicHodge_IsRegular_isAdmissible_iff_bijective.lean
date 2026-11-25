-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_isAdmissible_iff_bijective
-- name    : GroundTheory.PAdicHodge.IsRegular.isAdmissible_iff_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:09.986439+00:00
-- url     : https://prove2.me/theorems/25e1045c-eda0-4579-93da-f6c30990d69a
-- title:
--   Is Regular: is Admissible iff bijective
-- statement:
--   The Is Regular construction uses the is Admissible iff bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L304-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L304-L311

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

theorem GroundTheory.PAdicHodge.IsRegular.isAdmissible_iff_bijective [FiniteDimensional F V] :
    IsAdmissible B ρ ↔ Function.Bijective (comparison B ρ) := by sorry
