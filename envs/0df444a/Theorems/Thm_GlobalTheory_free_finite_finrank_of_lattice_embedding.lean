-- Prove2me | Theorems.Thm_GlobalTheory_free_finite_finrank_of_lattice_embedding
-- name    : GlobalTheory.free_finite_finrank_of_lattice_embedding
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:20.018919+00:00
-- url     : https://prove2.me/theorems/670a739a-07aa-4111-881d-a7677f9177ba
-- title:
--   Global Theory: free finite finrank of lattice embedding
-- statement:
--   The Global Theory construction uses the free finite finrank of lattice embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqCexpQuadraticOfEquivalentFactors.lean#L106-L115

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
variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']

theorem GlobalTheory.free_finite_finrank_of_lattice_embedding {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : L →+ V) (hP : Function.Injective P)
    (hd : DiscreteTopology (range P)) (hs : Submodule.span ℝ (range P) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℝ V := by sorry
