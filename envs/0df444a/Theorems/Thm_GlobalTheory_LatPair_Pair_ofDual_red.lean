-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_ofDual_red
-- name    : GlobalTheory.LatPair.Pair.ofDual_red
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:40.807694+00:00
-- url     : https://prove2.me/theorems/3d6d9226-69d2-4d9f-a90e-b94628452389
-- title:
--   Pair: of Dual red
-- statement:
--   The Pair construction uses the of Dual red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L402-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L402-L402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
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
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]

theorem GlobalTheory.LatPair.Pair.ofDual_red (P : Pair k n) : ofDual P.lat ⟨P.red, P.red_ne⟩ = P := by sorry
