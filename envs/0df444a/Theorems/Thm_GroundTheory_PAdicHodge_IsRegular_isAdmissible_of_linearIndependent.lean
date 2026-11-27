-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_isAdmissible_of_linearIndependent
-- name    : GroundTheory.PAdicHodge.IsRegular.isAdmissible_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:03.740818+00:00
-- url     : https://prove2.me/theorems/3a0039d5-12f3-4196-a2d4-d49f499c8068
-- title:
--   Is Regular: is Admissible of linear Independent
-- statement:
--   The Is Regular construction uses the is Admissible of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L313-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L313-L321

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

theorem GroundTheory.PAdicHodge.IsRegular.isAdmissible_of_linearIndependent [FiniteDimensional F V] {ι : Type*} [Fintype ι]
    {x : ι → DB B ρ} (hx : LinearIndependent B (fun i => (x i : B ⊗[F] V)))
    (hcard : finrank F V ≤ Fintype.card ι) : IsAdmissible B ρ := by sorry
