-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_initial_sigma_clipped_exists
-- name    : OAI.TraceReconstruction.initial_sigma_clipped_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:50:43.340499+00:00
-- url     : https://prove2.me/theorems/e9d0f65c-5862-43eb-ab98-de1599a1f915
-- title:
--   OAI.TraceReconstruction.initial_sigma_clipped_exists: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.initial_sigma_clipped_exists` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem initial_sigma_clipped_exists {Side : Type*} [Fintype Side] {J K m R : ℕ}
--       (M : PairedMechanisms Side J) (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m)
--       (hR : 0 < R) (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
--       (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
--       (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
--       (c : ℤ) (s k : ℕ) (hk : 1 ≤ k)
--       (hleft : (K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
--       (hright : (K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
--       {q ω w V : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
--       (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
--       (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
--       (hscale : initialMomentRatio K m q w ≤ 1/2)
--       (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
--       (hV : 0 ≤ V)
--       (hbudget : ∀z : InitialMetadata Side J (K*m),initialMetadataGood q ω z →
--         64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
--           ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
--       Nonempty (ClippedOracle
--         (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s (-1))
--         (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
--         (Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
--           (initialMetadataLaw M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
--             (fun z => if initialMetadataGood q ω z then 0 else 1)) V)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.ClippedOracle`, `OAI.TraceReconstruction.InitialMetadata`, `OAI.TraceReconstruction.InitialObservation`, `OAI.TraceReconstruction.PairedMechanisms`, `OAI.TraceReconstruction.PrimitiveMark`, `OAI.TraceReconstruction.Reports`, `OAI.TraceReconstruction.SafeTaggedTuple`, `OAI.TraceReconstruction.initialMetadataGood`, `OAI.TraceReconstruction.initialMetadataLaw`, `OAI.TraceReconstruction.initialMomentRatio`, `OAI.TraceReconstruction.initialSigmaLaw`, `OAI.TraceReconstruction.initialSignedBudget`, `OAI.TraceReconstruction.periodSlot`, `OAI.TraceReconstruction.posteriorAnchorSeries` and `OAI.TraceReconstruction.FiniteLaw.expect` (definitions bundle `OAIQ9Tr000` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.actual_initial_oracles` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean (declaration OAI.TraceReconstruction.initial_sigma_clipped_exists)

import Mathlib
import Definitions.Def_OAIQ9Tr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initial_sigma_clipped_exists {Side : Type*} [Fintype Side] {J K m R : ℕ}
    (M : PairedMechanisms Side J) (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m)
    (hR : 0 < R) (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (c : ℤ) (s k : ℕ) (hk : 1 ≤ k)
    (hleft : (K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
    {q ω w V : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V)
    (hbudget : ∀z : InitialMetadata Side J (K*m),initialMetadataGood q ω z →
      64*initialSignedBudget K m z.2.val R s (posteriorAnchorSeries c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
    Nonempty (ClippedOracle
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s (-1))
      (initialSigmaLaw M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
      (Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k)+
        (initialMetadataLaw M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
          (fun z => if initialMetadataGood q ω z then 0 else 1)) V) := by
  sorry

end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
end
