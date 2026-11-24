-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_latInd_mem_SB
-- name    : GlobalTheory.LatPair.latInd_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:20.504849+00:00
-- url     : https://prove2.me/theorems/1820354b-fe9c-40f1-8263-d93c8c9429a4
-- title:
--   Lat Pair: lat Ind mem SB
-- statement:
--   The Lat Pair construction uses the lat Ind mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L72-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']

theorem GlobalTheory.LatPair.latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k] [L.IsLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by sorry
