-- Prove2me | Theorems.Thm_OAI_Ostmann_projectedTree_mean_le
-- name    : OAI.Ostmann.projectedTree_mean_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:39.883332+00:00
-- url     : https://prove2.me/theorems/51e2e19f-1d8c-4bc3-8235-ed15ee68a306
-- title:
--   OAI.Ostmann.projectedTree_mean_le: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.projectedTree_mean_le` of [lean/OAI/NumberTheory/Ostmann/Characters/QuartetOuterAverage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/QuartetOuterAverage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem projectedTree_mean_le {p : ℕ} [Fact p.Prime]
--       (g : ZMod p → ℂ) (hg : g 0 = 0)
--       (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
--       (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
--       (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
--       (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
--       (c : TreeLeafTuple Bool (n + 2)) (cL cR : TreeLeafIndex n → Bool)
--       (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
--       (choice : TreeLeafIndex n → QuartetMovingCase)
--       (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
--       (hs : ∀ q j, sign (quartetLeafIndex n q j) =
--         treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
--       (i : TreeLeafIndex n) (hi : δ i = 1 ∨ δ i = -1) :
--       (∑ m : TreeLeafTuple (ZMod p)ˣ (n + 2),
--         ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
--           (treeLeafTupleEquiv _ (n + 2) m)‖ ^ 2) /
--         (Fintype.card (TreeLeafTuple (ZMod p)ˣ (n + 2)) : ℝ) ≤
--         (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
--           (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.MixedFourierBound`, `OAI.Ostmann.QuartetMovingCase`, `OAI.Ostmann.RationalTreeData`, `OAI.Ostmann.TreeLeafIndex`, `OAI.Ostmann.TreeLeafTuple`, `OAI.Ostmann.indexedRationalAmplitude`, `OAI.Ostmann.quartetBlockEquiv`, `OAI.Ostmann.treeLeafMap` and `OAI.Ostmann.treeLeafTupleEquiv` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.cycleAverage` and `OAI.Ostmann.quartetLocalMeanError` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.quartetLeafIndex`, `OAI.Ostmann.quartetMovingSign` and `OAI.Ostmann.treeLeafTupleFintype` (definitions bundle `OAIQ095D004` of this split).
--
--   **Used by.** The proof of `OAI.Ostmann.exists_movingPatternPrimeGain_window` of this split imports it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/QuartetOuterAverage.lean (declaration OAI.Ostmann.projectedTree_mean_le)

import Mathlib
import Definitions.Def_OAIQ095D004

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem projectedTree_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (i : TreeLeafIndex n) (hi : δ i = 1 ∨ δ i = -1) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ (n + 2),
      ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
        (treeLeafTupleEquiv _ (n + 2) m)‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ (n + 2)) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
  sorry

end Ostmann

end OAI
end
