-- Prove2me | Theorems.Thm_GlobalTheory_PrimeMeanValue_mem_primesIoc
-- name    : GlobalTheory.PrimeMeanValue.mem_primesIoc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:53.126559+00:00
-- url     : https://prove2.me/theorems/f96d6e18-8e77-49b7-804c-feed2c29f384
-- title:
--   Prime Mean Value: mem primes Ioc
-- statement:
--   The Prime Mean Value construction uses the mem primes Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L107-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue

theorem GlobalTheory.PrimeMeanValue.mem_primesIoc {x y : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesIoc x y ↔ x < p ∧ (p : ℝ) ≤ y ∧ p.Prime := by sorry
