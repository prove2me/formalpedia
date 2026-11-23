-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_cross_up_ofDual
-- name    : GlobalTheory.LatPair.cross_up_ofDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:12.2648+00:00
-- url     : https://prove2.me/theorems/b253aed2-a923-4372-8b43-dd54d9fad144
-- title:
--   Lat Pair: cross up of Dual
-- statement:
--   The Lat Pair construction uses the cross up of Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L499-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L499-L503

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

theorem GlobalTheory.LatPair.cross_up_ofDual (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (x : {x : Red L // x ≠ 0})
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : cross q (up L q x) (ofDual L f) = f.1 x.1 := by sorry
