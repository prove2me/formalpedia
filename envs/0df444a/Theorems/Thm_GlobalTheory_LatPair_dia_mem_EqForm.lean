-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm
-- name    : GlobalTheory.LatPair.dia_mem_EqForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:53.045141+00:00
-- url     : https://prove2.me/theorems/cf157082-c07d-43ec-9d53-da053c6f467a
-- title:
--   Lat Pair: dia mem Eq Form
-- statement:
--   The Lat Pair construction uses the dia mem Eq Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L246-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L246-L247

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

theorem GlobalTheory.LatPair.dia_mem_EqForm (c : 𝓀[k]ˣ) (h : φ ∈ EqForm π) : dia c φ ∈ EqForm π := by sorry
