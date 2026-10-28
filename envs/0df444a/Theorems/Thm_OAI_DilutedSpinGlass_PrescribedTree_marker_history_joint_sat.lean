-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_marker_history_joint_sat
-- name    : OAI.DilutedSpinGlass.PrescribedTree.marker_history_joint_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:56.059631+00:00
-- url     : https://prove2.me/theorems/d92604ea-05ea-4807-9064-b66d5da4adb6
-- title:
--   OAI.DilutedSpinGlass.PrescribedTree.marker_history_joint_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PrescribedTree.marker_history_joint` of [lean/OAI/Probability/DilutedSpin/MarkerNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MarkerNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PrescribedTree`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem marker_history_joint_sat (S T Q : PrescribedTree n) (a : S.Leaf)
--       (q : Option C → T.Leaf) (hq : Function.Bijective q)
--       (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
--       (hqQ : Function.Bijective (Sum.elim qold qfresh))
--       (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
--       (hmarker : ∀ x y, splitDepth T (q x) (q y)=
--         splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
--       (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
--       (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
--       (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
--       (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
--       (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
--       weightedMatrixHistory T q
--         (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
--         m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
--         (fun z => F (fun d => S.pathAt d z)) =
--       partialKappa T m (Finset.univ.image q) *
--         (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
--           A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.Sample`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafFintype`, `OAI.DilutedSpinGlass.PrescribedTree.markerNormalizationPropDecidable`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.pathAt`, `OAI.DilutedSpinGlass.PrescribedTree.sampleFintype`, `OAI.DilutedSpinGlass.PrescribedTree.sampleLaw`, `OAI.DilutedSpinGlass.PrescribedTree.splitDepth` and `OAI.DilutedSpinGlass.PrescribedTree.weightedMatrixHistory` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/MarkerNormalization.lean (declaration OAI.DilutedSpinGlass.PrescribedTree.marker_history_joint)

import Mathlib
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] {n : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.markerNormalizationPropDecidable
theorem marker_history_joint_sat (S T Q : PrescribedTree n) (a : S.Leaf)
    (q : Option C → T.Leaf) (hq : Function.Bijective q)
    (qold : S.Leaf → Q.Leaf) (qfresh : C → Q.Leaf)
    (hqQ : Function.Bijective (Sum.elim qold qfresh))
    (hold : ∀ d e, splitDepth S d e=splitDepth Q (qold d) (qold e))
    (hmarker : ∀ x y, splitDepth T (q x) (q y)=
      splitDepth Q (Option.elim' (qold a) qfresh x) (Option.elim' (qold a) qfresh y))
    (hsep : ∀ c d, splitDepth Q (qfresh c) (qold a) < splitDepth Q (qold a) (qold d))
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n)=1)
    (cs : List C) (hcs : cs.Nodup) (hfull : cs.toFinset=Finset.univ)
    (F : (S.Leaf → FinitePath Ω n) → ℝ) (A : (Option C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun R pos g => (R.sampleLaw K).expect (fun z => g z*A (fun c => R.pathAt (pos c) z)))
      m (cs.map some) S (Finset.univ.erase a) id (fun _ => a)
      (fun z => F (fun d => S.pathAt d z)) =
    partialKappa T m (Finset.univ.image q) *
      (Q.sampleLaw K).expect (fun z => F (fun d => Q.pathAt (qold d) z) *
        A (fun c => Q.pathAt (Option.elim' (qold a) qfresh c) z)) := by
  sorry

end DilutedSpinGlass.PrescribedTree

end

end OAI
end
