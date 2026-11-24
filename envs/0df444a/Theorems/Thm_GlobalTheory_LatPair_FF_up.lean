-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_FF_up
-- name    : GlobalTheory.LatPair.FF_up
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:56.102155+00:00
-- url     : https://prove2.me/theorems/08e2d38f-f200-46eb-aecf-470877887cad
-- title:
--   Lat Pair: FF up
-- statement:
--   The Lat Pair construction uses the FF up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L132-L134

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
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]

theorem GlobalTheory.LatPair.FF_up [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (x : {x : Red L // x ≠ 0}) :
    FF q χ φ (up L q x) = ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, χ (f.1 x.1) • φ (ofDual L f) := by sorry
