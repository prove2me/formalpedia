-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_FFStar_ofDual
-- name    : GlobalTheory.LatPair.FFStar_ofDual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:30.550198+00:00
-- url     : https://prove2.me/theorems/b7cd41e6-cc8a-4b86-943d-d28c56b317d3
-- title:
--   Lat Pair: FFStar of Dual
-- statement:
--   The Lat Pair construction uses the FFStar of Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L136-L138

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

theorem GlobalTheory.LatPair.FFStar_ofDual [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    FFStar q χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L q x) := by sorry
