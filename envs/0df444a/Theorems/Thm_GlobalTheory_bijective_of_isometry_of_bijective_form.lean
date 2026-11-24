-- Prove2me | Theorems.Thm_GlobalTheory_bijective_of_isometry_of_bijective_form
-- name    : GlobalTheory.bijective_of_isometry_of_bijective_form
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:56.439135+00:00
-- url     : https://prove2.me/theorems/f67ba089-a9c1-4d92-8957-5a3eae00ba4b
-- title:
--   Global Theory: bijective of isometry of bijective form
-- statement:
--   The Global Theory construction uses the bijective of isometry of bijective form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L86-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory

theorem GlobalTheory.bijective_of_isometry_of_bijective_form {R L L' : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
    [AddCommGroup L'] [Module R L'] [Module.Free R L'] [Module.Finite R L']
    (hrk : Module.finrank R L = Module.finrank R L')
    (E : LinearMap.BilinForm R L) (E' : LinearMap.BilinForm R L') (hE : Function.Bijective E)
    (g : L →ₗ[R] L') (hg : ∀ a b, E' (g a) (g b) = E a b) : Function.Bijective g := by sorry
