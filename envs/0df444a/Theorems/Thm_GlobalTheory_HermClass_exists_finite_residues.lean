-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_finite_residues
-- name    : GlobalTheory.HermClass.exists_finite_residues
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:52.601956+00:00
-- url     : https://prove2.me/theorems/761d2a38-db56-4de2-9eca-9bc0cf0e534b
-- title:
--   Herm Class: exists finite residues
-- statement:
--   The Herm Class construction uses the exists finite residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L8-L29

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
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

theorem GlobalTheory.HermClass.exists_finite_residues {V : Type} [AddCommGroup V] (L : Submodule ℤ V) (hL : L.FG)
    {m : ℤ} (hm : m ≠ 0) :
    ∃ R : Set V, R.Finite ∧ (∀ ρ ∈ R, ρ ∈ L) ∧ ∀ x ∈ L, ∃ ρ ∈ R, ∃ y ∈ L, x = ρ + m • y := by sorry
