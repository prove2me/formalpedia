-- Prove2me | Theorems.Thm_OAI_DFVSGames_Inverse_KMSMomentTheorem_lifted_fourth_moment_bound
-- name    : OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:01:30.852378+00:00
-- url     : https://prove2.me/theorems/fca84b62-0d15-4518-affb-11c4c9110a2d
-- title:
--   OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of [lean/OAI/Computability/DirectedFeedback/Analysis/KMSMomentScalar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Analysis/KMSMomentScalar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Inverse.KMSMomentTheorem`, with `open scoped BigOperators Classical`, `open KMS KMSBasisComparison KMSBasisComparisonPseudorandom`, `open KMSAnalytic KMSFourthMoment KMSMomentConstants`):
--
--   ```lean
--   theorem lifted_fourth_moment_bound
--       (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
--       (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
--       (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
--       (i : ℕ) (hi : i ≤ r) :
--       (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
--         fourthMomentConstant r *
--           (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Inverse.KMS.Ambient`, `OAI.DFVSGames.Inverse.KMS.F2`, `OAI.DFVSGames.Inverse.KMS.Vertex`, `OAI.DFVSGames.Inverse.KMSBasisComparison.BasisMap`, `OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype`, `OAI.DFVSGames.Inverse.KMSBasisComparison.liftedIndicator`, `OAI.DFVSGames.Inverse.KMSBasisComparisonPseudorandom.TuplePseudorandom` and `OAI.DFVSGames.Inverse.KMSMomentConstants.fourthMomentConstant` (definitions bundle `OAIQ085D003` of this split); `OAI.DFVSGames.Inverse.KMSAnalytic.rankComponent` (definitions bundle `OAIQ085D027` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.theorem11` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Analysis/KMSMomentScalar.lean (declaration OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound)

import Mathlib
import Definitions.Def_OAIQ085D027

section

attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

theorem lifted_fourth_moment_bound
    (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
    (i : ℕ) (hi : i ≤ r) :
    (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
      fourthMomentConstant r *
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε := by
  sorry

end
end DFVSGames.Inverse.KMSMomentTheorem

end OAI
end
