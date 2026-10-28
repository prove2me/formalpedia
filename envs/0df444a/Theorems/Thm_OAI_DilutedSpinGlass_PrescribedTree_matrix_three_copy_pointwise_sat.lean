-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_matrix_three_copy_pointwise_sat
-- name    : OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:22.909913+00:00
-- url     : https://prove2.me/theorems/22cf211b-59bb-48ca-b66b-2b713d26a3b1
-- title:
--   OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise` of [lean/OAI/Probability/DilutedSpin/MatrixTriple.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MatrixTriple.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PrescribedTree`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem matrix_three_copy_pointwise_sat (hL : 0 < L) (Q : Finset ℕ)
--       (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
--       (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
--       (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
--       (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
--       (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
--       (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
--       (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
--       (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
--       (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
--       (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
--       (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
--       let m := grid L 0 L
--       let J := partialKappa T m (Finset.univ.image q) /
--         partialKappa T m ((insert c ({a} : Finset C)).image q)
--       let H := weightedMatrixHistory T q
--         (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
--         m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
--       let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
--         FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
--       let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
--         ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
--         (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
--       (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
--         (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
--         pairHistoryMass S m x * (S.sampleLaw K).l2
--           (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.FiniteLaw.dot`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.FiniteLaw.l2`, `OAI.DilutedSpinGlass.KernelTower.halfTripleDifferenceAt`, `OAI.DilutedSpinGlass.PrescribedTree.Internal`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.Sample`, `OAI.DilutedSpinGlass.PrescribedTree.branchingCount`, `OAI.DilutedSpinGlass.PrescribedTree.chargeBound`, `OAI.DilutedSpinGlass.PrescribedTree.freshSplitDepth`, `OAI.DilutedSpinGlass.PrescribedTree.gamma`, `OAI.DilutedSpinGlass.PrescribedTree.grid`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafFintype`, `OAI.DilutedSpinGlass.PrescribedTree.leaves`, `OAI.DilutedSpinGlass.PrescribedTree.pairHistoryMass`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.pathAt`, `OAI.DilutedSpinGlass.PrescribedTree.sampleFintype`, `OAI.DilutedSpinGlass.PrescribedTree.sampleLaw`, `OAI.DilutedSpinGlass.PrescribedTree.splitDepth` and `OAI.DilutedSpinGlass.PrescribedTree.weightedMatrixHistory` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MatrixTriple.lean (declaration OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise)

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
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

theorem matrix_three_copy_pointwise_sat (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
    let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
      FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
    let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  sorry

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end
