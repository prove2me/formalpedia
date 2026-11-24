-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_GsStar_apply
-- name    : GlobalTheory.LatPair.GsStar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:50.188664+00:00
-- url     : https://prove2.me/theorems/b628454e-ca15-4ed4-bac9-c676701e748b
-- title:
--   Lat Pair: Gs Star apply
-- statement:
--   The Lat Pair construction uses the Gs Star apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L98-L101

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

theorem GlobalTheory.LatPair.GsStar_apply [Fintype 𝓀[k]ˣ] (P : Pair k n) :
    GsStar χ φ P = ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • φ (c⁻¹ • P) := by sorry
