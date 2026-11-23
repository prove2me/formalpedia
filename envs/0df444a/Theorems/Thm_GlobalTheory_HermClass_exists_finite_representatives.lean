-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_finite_representatives
-- name    : GlobalTheory.HermClass.exists_finite_representatives
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:20.690161+00:00
-- url     : https://prove2.me/theorems/5bd4a3a3-8147-4bf7-a790-1643233a435a
-- title:
--   Herm Class: exists finite representatives
-- statement:
--   The Herm Class construction uses the exists finite representatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteRepresentatives.lean#L47-L53

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

theorem GlobalTheory.HermClass.exists_finite_representatives {α : Type*} {β : Type*} (f : α → β)
    (hf : (Set.range f).Finite) : ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, f s = f a := by sorry
