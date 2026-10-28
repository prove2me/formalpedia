-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_actual_initial_oracles
-- name    : OAI.TraceReconstruction.actual_initial_oracles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:50:42.775443+00:00
-- url     : https://prove2.me/theorems/0195dc7f-0361-4672-a118-feceba006383
-- title:
--   OAI.TraceReconstruction.actual_initial_oracles: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.actual_initial_oracles` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem actual_initial_oracles {J K m R : ℕ}
--       (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m) (hR : 0 < R)
--       (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
--       (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
--       (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
--       (a : ℤ) (s k : ℕ) (hk : 1 ≤ k) {q w V W : ℝ}
--       (hq : q∈Set.Ioc 0 (1/2:ℝ))
--       (hseed : 16 ≤ q^3*(m:ℝ)) (hcount : 8 ≤ ((K*m:ℕ):ℝ)*q^2)
--       (ha : (J*initialSideCount q m+J:ℕ) ≤ a)
--       (ha' : a+(2^s:ℕ) ≤ (J*initialSideCount q m+K:ℕ))
--       (hleft : (K:ℝ)/3 ≤ 2*((a-(J*initialSideCount q m:ℕ):ℤ)-J)+1)
--       (hright : (K:ℝ)/3 ≤ 2*K-(2*((a-(J*initialSideCount q m:ℕ):ℤ)+(2:ℝ)^s)+1))
--       (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
--       (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
--       (hscale : initialMomentRatio K m q w ≤ 1/2)
--       (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
--       (hV : 0 ≤ V) (hW : 0 ≤ W)
--       (hSV : 64*initialSignedCap J K m R s q (initialOverlapLower q) w ≤ V)
--       (hPW : 64*initialPureCap J K m R s q (initialOverlapLower q) w ≤ W) :
--       Nonempty (OracleTracePair q
--         (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a (-1))
--         (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
--         (initialErrorCap J K m k q (initialOverlapLower q) w) V) ∧
--       Nonempty (OracleTracePair q
--         (pureAtomRun (initialPeriod m off.val) (J*(2*initialSideCount q m+1)+K))
--         (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
--         (initialErrorCap J K m k q (initialOverlapLower q) w) W)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.OracleTracePair`, `OAI.TraceReconstruction.SafeTaggedTuple`, `OAI.TraceReconstruction.initialErrorCap`, `OAI.TraceReconstruction.initialMomentRatio`, `OAI.TraceReconstruction.initialOverlapLower`, `OAI.TraceReconstruction.initialPeriod`, `OAI.TraceReconstruction.initialPureCap`, `OAI.TraceReconstruction.initialSideCount`, `OAI.TraceReconstruction.initialSignedCap`, `OAI.TraceReconstruction.motifPeriodWord`, `OAI.TraceReconstruction.periodSlot` and `OAI.TraceReconstruction.pureAtomRun` (definitions bundle `OAIQ9Tr000` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.source_initial_oracles_eventually` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/InitialOracle.lean (declaration OAI.TraceReconstruction.actual_initial_oracles)

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

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem actual_initial_oracles {J K m R : ℕ}
    (hK : 0 < K) (hm : 128 ≤ m) (hKm : K ≤ m) (hR : 0 < R)
    (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (hoff : |(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe : SafeTaggedTuple (periodSlot (u:=K) (fun _ => off)))
    (a : ℤ) (s k : ℕ) (hk : 1 ≤ k) {q w V W : ℝ}
    (hq : q∈Set.Ioc 0 (1/2:ℝ))
    (hseed : 16 ≤ q^3*(m:ℝ)) (hcount : 8 ≤ ((K*m:ℕ):ℝ)*q^2)
    (ha : (J*initialSideCount q m+J:ℕ) ≤ a)
    (ha' : a+(2^s:ℕ) ≤ (J*initialSideCount q m+K:ℕ))
    (hleft : (K:ℝ)/3 ≤ 2*((a-(J*initialSideCount q m:ℕ):ℤ)-J)+1)
    (hright : (K:ℝ)/3 ≤ 2*K-(2*((a-(J*initialSideCount q m:ℕ):ℤ)+(2:ℝ)^s)+1))
    (hM : ((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw : w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale : initialMomentRatio K m q w ≤ 1/2)
    (hclip : Real.sqrt (6*(4*(initialMomentRatio K m q w/(1-initialMomentRatio K m q w)))^k) ≤ 1/2)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hSV : 64*initialSignedCap J K m R s q (initialOverlapLower q) w ≤ V)
    (hPW : 64*initialPureCap J K m R s q (initialOverlapLower q) w ≤ W) :
    Nonempty (OracleTracePair q
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a (-1))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) V) ∧
    Nonempty (OracleTracePair q
      (pureAtomRun (initialPeriod m off.val) (J*(2*initialSideCount q m+1)+K))
      (motifPeriodWord off hi (J*(2*initialSideCount q m+1)+K) s a 1) k
      (initialErrorCap J K m k q (initialOverlapLower q) w) W) := by
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
