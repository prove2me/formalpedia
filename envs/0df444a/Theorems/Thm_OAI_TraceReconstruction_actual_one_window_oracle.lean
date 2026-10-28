-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_actual_one_window_oracle
-- name    : OAI.TraceReconstruction.actual_one_window_oracle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:52:22.765965+00:00
-- url     : https://prove2.me/theorems/9efd2d7c-4535-478e-b4c9-a472c87727b7
-- title:
--   OAI.TraceReconstruction.actual_one_window_oracle: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.actual_one_window_oracle` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Amplification.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Amplification.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem actual_one_window_oracle {q E V : ℝ} {x y : List Bool} {k : ℕ}
--       (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E)
--       (s N T t h R : ℕ) (hT : 24 ≤ T) (he : Even T)
--       (hMotif : 24*2^s ≤ T) (hroot : 4*(t+1) ≤ T)
--       (hfit : t*(2*h+1)+T ≤ N)
--       (ω a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hω : ω∈Set.Ioo 0 1)
--       (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1)))
--       (hk : 1 ≤ k) (hV : V ≤ L^2)
--       (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
--       (hη : hiddenSmoothingBound t s ω ≤ η)
--       (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L ≤ 1/2) :
--       Nonempty (OracleTracePair q
--         (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) false)
--         (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) true) k
--         (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L+(T:ℝ)*E)
--         (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 R ω η a ((6*(2*k:ℕ):ℝ)*L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.OracleTracePair`, `OAI.TraceReconstruction.complementaryWords`, `OAI.TraceReconstruction.hiddenSmoothingBound`, `OAI.TraceReconstruction.listTraceOverlap`, `OAI.TraceReconstruction.prouhetBool`, `OAI.TraceReconstruction.pureAtomRun` and `OAI.TraceReconstruction.sourceSparseCount` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceClippingCost` and `OAI.TraceReconstruction.sourceSharpEnergyBudget` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.source_level_overlap` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Amplification.lean (declaration OAI.TraceReconstruction.actual_one_window_oracle)

import Mathlib
import Definitions.Def_OAIQ9Tr002

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
namespace TraceReconstruction
open scoped Classical

theorem actual_one_window_oracle {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E)
    (s N T t h R : ℕ) (hT : 24 ≤ T) (he : Even T)
    (hMotif : 24*2^s ≤ T) (hroot : 4*(t+1) ≤ T)
    (hfit : t*(2*h+1)+T ≤ N)
    (ω a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hω : ω∈Set.Ioo 0 1)
    (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1)))
    (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
    (hη : hiddenSmoothingBound t s ω ≤ η)
    (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L ≤ 1/2) :
    Nonempty (OracleTracePair q
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) false)
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) true) k
      (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L+(T:ℝ)*E)
      (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  sorry

end TraceReconstruction

end
end
end
end
end

end OAI
end
