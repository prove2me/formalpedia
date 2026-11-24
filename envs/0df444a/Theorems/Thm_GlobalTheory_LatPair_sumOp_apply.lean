-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_sumOp_apply
-- name    : GlobalTheory.LatPair.sumOp_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:33.560844+00:00
-- url     : https://prove2.me/theorems/d1a29ccd-662e-46c8-aab4-40a1e3854a27
-- title:
--   Lat Pair: sum Op apply
-- statement:
--   The Lat Pair construction uses the sum Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L84-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)

theorem GlobalTheory.LatPair.sumOp_apply (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (P : Pair k n) :
    sumOp S w φ P = ∑ Q ∈ S P, w P Q • φ Q := by sorry
