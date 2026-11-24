-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
-- name    : GlobalTheory.LatPair.isClopen_lattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:12.776915+00:00
-- url     : https://prove2.me/theorems/701e5bb1-e8e4-474c-9705-90828475c541
-- title:
--   Lat Pair: is Clopen lattice
-- statement:
--   The Lat Pair construction uses the is Clopen lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L23-L34

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

theorem GlobalTheory.LatPair.isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsClopen (L : Set (n → k)) := by sorry
