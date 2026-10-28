-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_matrixHistory_first_pair_sat
-- name    : OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:56.290527+00:00
-- url     : https://prove2.me/theorems/4a1f1e5f-92b3-457c-9531-691af22408dd
-- title:
--   OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair` of [lean/OAI/Probability/DilutedSpin/MatrixPair.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MatrixPair.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PrescribedTree`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem matrixHistory_first_pair_sat (T : PrescribedTree n) (q : C → T.Leaf)
--       (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
--       (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
--       (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
--       (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
--       (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
--       (S : PrescribedTree n) (x : S.Leaf)
--       (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
--       weightedMatrixHistory T q
--         (fun D pos g => (D.sampleLaw K).expect
--           (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
--         m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f =
--       (partialKappa T m (Finset.univ.image q) /
--         partialKappa T m ((insert c ({a} : Finset C)).image q)) *
--         pairObservableHistory K m S x (splitDepth T (q a) (q c)) R f
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.Sample`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafFintype`, `OAI.DilutedSpinGlass.PrescribedTree.pairObservableHistory`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.pathAt`, `OAI.DilutedSpinGlass.PrescribedTree.sampleFintype`, `OAI.DilutedSpinGlass.PrescribedTree.sampleLaw`, `OAI.DilutedSpinGlass.PrescribedTree.splitDepth` and `OAI.DilutedSpinGlass.PrescribedTree.weightedMatrixHistory` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MatrixPair.lean (declaration OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair)

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
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

theorem matrixHistory_first_pair_sat (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect
        (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f =
    (partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)) *
      pairObservableHistory K m S x (splitDepth T (q a) (q c)) R f := by
  sorry

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end
