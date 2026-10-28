-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_root_matrix_three_copy_sat
-- name    : OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:26.644503+00:00
-- url     : https://prove2.me/theorems/634575d8-47c1-4088-b053-98a6da0a16f9
-- title:
--   OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy` of [lean/OAI/Probability/DilutedSpin/RootMatrixTriple.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootMatrixTriple.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PrescribedTree`, with `open _root_.MeasureTheory`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem root_matrix_three_copy_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
--       [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
--       (hL : 0 < L) (Q : Finset ℕ) (T S : PrescribedTree L)
--       (q : C → T.Leaf) (hq : Function.Bijective q) (hS : branchingCount S (· ∈ Q) = 0)
--       (K : (z : Z) → KernelTower (Ω z) L)
--       (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
--       (hdis : ∀ b ∈ cs, b ∉ insert c ({a} : Finset C))
--       (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
--       (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
--       (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
--       (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
--       (X : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hX : ∀ z w i, |X z w i| ≤ 1)
--       (hOld : ∀ z b, splitDepth S x b = d → ∀ w : Sample (Ω z) S,
--         X z (S.pathAt b w) = X z (S.pathAt y w))
--       (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ) (hA : ∀ z w, |A z w| ≤ 1)
--       (f : (z : Z) → Sample (Ω z) S → ℝ) (hf : ∀ z w, |f z w| ≤ 1)
--       (hE : Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ)
--       (hH : Integrable (fun z => matrixObservableHistory T q (K z) (grid L 0 L) (c::cs) S x (A z) (f z)) μ)
--       (hEt : Integrable (fun z => matrixProjectionError T q (K z) a c (A z) (X z)) μ)
--       (hEo : Integrable (fun z => oldProjectionError S (K z) x y (f z) (X z)) μ)
--       (hMean : Integrable (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w))) μ) :
--       let m := grid L 0 L
--       let J := partialKappa T m (Finset.univ.image q) /
--         partialKappa T m ((insert c ({a} : Finset C)).image q)
--       (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
--         2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
--           |matrixRootCovariance μ Ω T S q K m (c::cs) x A f|/|J| +
--           (∫ z, matrixProjectionError T q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q T S (c::cs).length/|J| +
--           pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (f z) (X z) ∂μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.KernelTower.halfTripleDifferenceAt`, `OAI.DilutedSpinGlass.PrescribedTree.Internal`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.Sample`, `OAI.DilutedSpinGlass.PrescribedTree.branchingCount`, `OAI.DilutedSpinGlass.PrescribedTree.freshSplitDepth`, `OAI.DilutedSpinGlass.PrescribedTree.gamma`, `OAI.DilutedSpinGlass.PrescribedTree.grid`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.matrixObservableHistory`, `OAI.DilutedSpinGlass.PrescribedTree.matrixProjectionError`, `OAI.DilutedSpinGlass.PrescribedTree.matrixRootCovariance`, `OAI.DilutedSpinGlass.PrescribedTree.oldProjectionError`, `OAI.DilutedSpinGlass.PrescribedTree.pairHistoryMass`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.pathAt`, `OAI.DilutedSpinGlass.PrescribedTree.sampleFintype`, `OAI.DilutedSpinGlass.PrescribedTree.sampleLaw`, `OAI.DilutedSpinGlass.PrescribedTree.shiftedCharge` and `OAI.DilutedSpinGlass.PrescribedTree.splitDepth` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootMatrixTriple.lean (declaration OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy)

import Mathlib
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators Classical
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

theorem root_matrix_three_copy_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (hL : 0 < L) (Q : Finset ℕ) (T S : PrescribedTree L)
    (q : C → T.Leaf) (hq : Function.Bijective q) (hS : branchingCount S (· ∈ Q) = 0)
    (K : (z : Z) → KernelTower (Ω z) L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ b ∈ cs, b ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hX : ∀ z w i, |X z w i| ≤ 1)
    (hOld : ∀ z b, splitDepth S x b = d → ∀ w : Sample (Ω z) S,
      X z (S.pathAt b w) = X z (S.pathAt y w))
    (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ) (hA : ∀ z w, |A z w| ≤ 1)
    (f : (z : Z) → Sample (Ω z) S → ℝ) (hf : ∀ z w, |f z w| ≤ 1)
    (hE : Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ)
    (hH : Integrable (fun z => matrixObservableHistory T q (K z) (grid L 0 L) (c::cs) S x (A z) (f z)) μ)
    (hEt : Integrable (fun z => matrixProjectionError T q (K z) a c (A z) (X z)) μ)
    (hEo : Integrable (fun z => oldProjectionError S (K z) x y (f z) (X z)) μ)
    (hMean : Integrable (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w))) μ) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
      2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
        |matrixRootCovariance μ Ω T S q K m (c::cs) x A f|/|J| +
        (∫ z, matrixProjectionError T q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q T S (c::cs).length/|J| +
        pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (f z) (X z) ∂μ) := by
  sorry

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end
