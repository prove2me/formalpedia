-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Model_colE_smul_gluedLat
-- name    : GlobalTheory.LatPair.Model.colE_smul_gluedLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:57.786811+00:00
-- url     : https://prove2.me/theorems/312a4cec-dd59-4655-8986-08bf7f67c007
-- title:
--   Model: col E smul glued Lat
-- statement:
--   The Model construction uses the col E smul glued Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L164-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsFFNeZeroThree.lean#L164-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
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
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.LatPair.Model.colE_smul_gluedLat [Fintype n] [DecidableEq n] (q : Unif k) {c p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c)
    (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.colE c p (-((q.1 : k) • f)) • gluedLat q c p L f = gluedLat q c p L 0 := by sorry
