-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_dia_hasVal_one
-- name    : GlobalTheory.LatPair.Pair.dia_hasVal_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:09.571576+00:00
-- url     : https://prove2.me/theorems/b1afbfa0-fc53-4725-b7bf-7f1034fd378b
-- title:
--   Pair: dia has Val one
-- statement:
--   The Pair construction uses the dia has Val one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L304-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L304-L307

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
open GlobalTheory.LatPair.Pair

theorem GlobalTheory.LatPair.Pair.dia_hasVal_one {c : 𝓀[k]ˣ} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) {s : 𝒪[k]}
    (hs : residue 𝒪[k] s = (c⁻¹ : 𝓀[k]ˣ)) : (c • P).HasVal (s • e) 1 := by sorry
