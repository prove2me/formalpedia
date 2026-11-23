-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_finite_between
-- name    : GlobalTheory.HermClass.finite_between
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:26.902549+00:00
-- url     : https://prove2.me/theorems/4f83720f-3ca8-4a36-8d29-f9fe17d1d847
-- title:
--   Herm Class: finite between
-- statement:
--   The Herm Class construction uses the finite between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L8-L45

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField

theorem GlobalTheory.HermClass.finite_between {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (L₀ : Submodule ℤ V) (h₀ : L₀.FG) {M : ℤ} (hM : M ≠ 0) :
    {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀}.Finite := by sorry
