-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_eq_glue_iff
-- name    : GlobalTheory.LatPair.eq_glue_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:08.253693+00:00
-- url     : https://prove2.me/theorems/f13b6e05-0333-447b-9051-10f2136905b3
-- title:
--   Lat Pair: eq glue iff
-- statement:
--   The Lat Pair construction uses the eq glue iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L231-L232

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
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}

theorem GlobalTheory.LatPair.eq_glue_iff (h : IsGlue L e) {P : Pair k n} : P = glue h ↔ P.ker = L ∧ P.HasVal e 1 := by sorry
