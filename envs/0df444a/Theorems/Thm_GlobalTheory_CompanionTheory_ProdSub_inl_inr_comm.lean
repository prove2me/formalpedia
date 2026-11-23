-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_inl_inr_comm
-- name    : GlobalTheory.CompanionTheory.ProdSub.inl_inr_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:26.13009+00:00
-- url     : https://prove2.me/theorems/c91dc14f-c631-4cda-b1ff-c03d81318343
-- title:
--   Prod Sub: inl inr comm
-- statement:
--   The Prod Sub construction uses the inl inr comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L157-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSub

theorem GlobalTheory.CompanionTheory.ProdSub.inl_inr_comm {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G × H) V) (g : G) (h : H) (x : V) :
    ρ (g, 1) (ρ (1, h) x) = ρ (1, h) (ρ (g, 1) x) := by sorry
