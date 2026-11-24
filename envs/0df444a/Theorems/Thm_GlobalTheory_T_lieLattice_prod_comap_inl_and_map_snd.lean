-- Prove2me | Theorems.Thm_GlobalTheory_T_lieLattice_prod_comap_inl_and_map_snd
-- name    : GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:58.191736+00:00
-- url     : https://prove2.me/theorems/9c25c2ca-b0b0-453c-bc84-660f85457960
-- title:
--   T: lie Lattice prod comap inl and map snd
-- statement:
--   The T construction uses the lie Lattice prod comap inl and map snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LieLatticeProdComapInlAndMapSndStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LieLatticeProdComapInlAndMapSndStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSndStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by sorry
