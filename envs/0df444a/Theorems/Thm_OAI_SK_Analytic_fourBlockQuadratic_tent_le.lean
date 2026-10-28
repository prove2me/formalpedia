-- Prove2me | Theorems.Thm_OAI_SK_Analytic_fourBlockQuadratic_tent_le
-- name    : OAI.SK.Analytic.fourBlockQuadratic_tent_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:58:52.809634+00:00
-- url     : https://prove2.me/theorems/ef8d0823-8faf-4833-ac5a-a52950ef6910
-- title:
--   OAI.SK.Analytic.fourBlockQuadratic_tent_le: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.fourBlockQuadratic_tent_le` of [lean/OAI/Probability/SKBarriers/SKBarriers/Locking/FourBlockQuadratic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/FourBlockQuadratic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators`, `open Set`):
--
--   ```lean
--   theorem fourBlockQuadratic_tent_le (κ η : ℝ) (b l j k t : List (ℝ × ℝ))
--       (hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1)
--       (hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1))
--       (hmean : 0≤weightedMean (fourBlockFuture η j k))
--       {d B : ℝ} (hd : 0<d) (hB : 0≤B) (hκ : κ*d=1)
--       (hl : rawVariance l=B*d) (hj : rawVariance j=B*d) :
--       narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤
--         narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
--           narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
--         2*weightedMean (fourBlockFuture η j k)*B*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
--         6*(weightedAbsCross (fourBlockFuture η j k))^2+
--         2*weightedMean (fourBlockFuture η j k)*B*scalarTentAtomMass (fourBlockTent κ b l j k).length
--           (fun i => ((fourBlockTent κ b l j k).get i).1) (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)+
--         (B*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
--           (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k))^2+
--         B^2*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
--           (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.rawVariance`, `OAI.SK.Analytic.weightedAbsCross` and `OAI.SK.Analytic.weightedMean` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.scalarTentAtomMass` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.fourBlockCommon`, `OAI.SK.Analytic.fourBlockFuture`, `OAI.SK.Analytic.fourBlockLeft`, `OAI.SK.Analytic.fourBlockRight`, `OAI.SK.Analytic.fourBlockTent` and `OAI.SK.Analytic.narrowVariance` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.narrowBaseQuadratic`, `OAI.SK.Analytic.narrowJointMoment` and `OAI.SK.Analytic.narrowSusceptibility` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.narrowConstrainedPressure_scaled_gap` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Locking/FourBlockQuadratic.lean (declaration OAI.SK.Analytic.fourBlockQuadratic_tent_le)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockQuadratic_tent_le (κ η : ℝ) (b l j k t : List (ℝ × ℝ))
    (hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1)
    (hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1))
    (hmean : 0≤weightedMean (fourBlockFuture η j k))
    {d B : ℝ} (hd : 0<d) (hB : 0≤B) (hκ : κ*d=1)
    (hl : rawVariance l=B*d) (hj : rawVariance j=B*d) :
    narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤
      narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
        narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      2*weightedMean (fourBlockFuture η j k)*B*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      6*(weightedAbsCross (fourBlockFuture η j k))^2+
      2*weightedMean (fourBlockFuture η j k)*B*scalarTentAtomMass (fourBlockTent κ b l j k).length
        (fun i => ((fourBlockTent κ b l j k).get i).1) (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)+
      (B*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k))^2+
      B^2*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k) := by
  sorry

end SK.Analytic

end
end

end OAI
end
