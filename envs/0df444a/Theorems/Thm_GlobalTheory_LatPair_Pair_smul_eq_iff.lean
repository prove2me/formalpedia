-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Pair_smul_eq_iff
-- name    : GlobalTheory.LatPair.Pair.smul_eq_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:00.149437+00:00
-- url     : https://prove2.me/theorems/caa7094f-7c0a-4821-96b9-b7b382581e1a
-- title:
--   Pair: smul eq iff
-- statement:
--   The Pair construction uses the smul eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L571-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L571-L575

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
variable [Fintype n] [DecidableEq n]
open GlobalTheory.LatPair.Pair

theorem GlobalTheory.LatPair.Pair.smul_eq_iff {g : GL n k} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) :
    g • P = P ↔ g • P.ker = P.ker ∧ g • e - e ∈ P.ker := by sorry
