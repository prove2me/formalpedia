-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_FFStar_mem_EqForm
-- name    : GlobalTheory.LatPair.FFStar_mem_EqForm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:48.671199+00:00
-- url     : https://prove2.me/theorems/5ae8b2e1-ec0a-40be-903e-ceaf09abddb8
-- title:
--   Lat Pair: FFStar mem Eq Form
-- statement:
--   The Lat Pair construction uses the FFStar mem Eq Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L255-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L255-L256

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
variable [Fintype n] [DecidableEq n]
variable (π : Representation ℂ (GL n k) M)
variable (g : GL n k) (P : Pair k n)
variable {π φ}

theorem GlobalTheory.LatPair.FFStar_mem_EqForm (h : φ ∈ EqForm π) : FFStar q χ φ ∈ EqForm π := by sorry
