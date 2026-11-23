-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_mem_fixed_iff_forall
-- name    : GlobalTheory.CompanionTheory.ProdSub.mem_fixed_iff_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:21.888087+00:00
-- url     : https://prove2.me/theorems/c00ead17-40cd-48e1-ab16-bba61b217e1c
-- title:
--   Prod Sub: mem fixed iff forall
-- statement:
--   The Prod Sub construction uses the mem fixed iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L14-L18

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
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ProdSub.mem_fixed_iff_forall {π : Representation ℂ G V} {K : Subgroup G} {x : V} :
    x ∈ fixed π K ↔ ∀ k ∈ K, π k x = x := by sorry
