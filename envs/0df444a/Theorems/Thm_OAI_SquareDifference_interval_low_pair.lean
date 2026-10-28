-- Prove2me | Theorems.Thm_OAI_SquareDifference_interval_low_pair
-- name    : OAI.SquareDifference.interval_low_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T12:08:51.100267+00:00
-- url     : https://prove2.me/theorems/2fa560bd-493f-4260-9590-b3d2e7260fd8
-- title:
--   OAI.SquareDifference.interval_low_pair: intermediate lemma from OpenAI, A power saving for square-difference-free sets
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SquareDifference.power_saving`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for square-difference-free sets*, OpenAI Math Release, September 24, 2026, result family 182, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SquareDifference.interval_low_pair` of [lean/OAI/Combinatorics/SquareDifference/IntervalPair.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SquareDifference/IntervalPair.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SquareDifference`, with `open Finset`, `open scoped BigOperators ComplexConjugate`, `open LiftTheory.SquareDifference PairBridge`):
--
--   ```lean
--   lemma interval_low_pair (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
--       (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
--       (hHQ : H*(∏j∈B,p j)≤Q)
--       (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
--       (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
--       (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
--       (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
--       (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
--       (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
--       ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
--         residueFourier (OutsideModulus p B)
--           (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ)) (-ξ)*
--         residueFourier (OutsideModulus p B)
--           (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ)) ξ*
--         squareMultiplier (OutsideModulus p B) ξ‖≤
--         ((N:ℝ)/L)^2*(smallModulus ps)*(∏j∈B,p j:ℝ)*
--           (kernelAbsoluteConstant*(H:ℝ)^(-(1:ℝ)/3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SquareDifference.NatSquareFree`, `OAI.SquareDifference.extendedPrime`, `OAI.SquareDifference.intervalLift`, `OAI.SquareDifference.kernelAbsoluteConstant`, `OAI.SquareDifference.smallModulus`, `OAI.SquareDifference.smallResidueInput`, `OAI.SquareDifference.smallStrictPair`, `OAI.LiftTheory.SquareDifference.OutsideModulus`, `OAI.LiftTheory.SquareDifference.ResidueSpace`, `OAI.LiftTheory.SquareDifference.residueFourier`, `OAI.LiftTheory.SquareDifference.squareMultiplier`, `OAI.LiftTheory.SquareDifference.supportDenominator` and `OAI.SquareDifference.PairBridge.assembleOutside` (definitions bundle `OAIB3Sq000` of this split).
--
--   **Used by.** The proof of `OAI.SquareDifference.source_ordered_contraction` of this split imports it.
-- source:
--   OpenAI, A power saving for square-difference-free sets, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 182; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SquareDifference/IntervalPair.lean (declaration OAI.SquareDifference.interval_low_pair)

import Mathlib
import Definitions.Def_OAIB3Sq000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section LowPair

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma interval_low_pair (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
    (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
    (hHQ : H*(∏j∈B,p j)≤Q)
    (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
    (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ)) (-ξ)*
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ)) ξ*
      squareMultiplier (OutsideModulus p B) ξ‖≤
      ((N:ℝ)/L)^2*(smallModulus ps)*(∏j∈B,p j:ℝ)*
        (kernelAbsoluteConstant*(H:ℝ)^(-(1:ℝ)/3)) := by
  sorry

end LowPair

end SquareDifference

end

end OAI
end
