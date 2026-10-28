-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_actual_source_oracle
-- name    : OAI.TraceReconstruction.actual_source_oracle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:51:42.247188+00:00
-- url     : https://prove2.me/theorems/b8cf15e4-500d-48f1-b9de-773cb9740166
-- title:
--   OAI.TraceReconstruction.actual_source_oracle: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.actual_source_oracle` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem actual_source_oracle {Leaf : Type} [Fintype Leaf]
--       {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
--       (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b R k : ℕ)
--       (H : SourceLayoutMargins s P T n h b)
--       (hTpos : ∀j,0<T j) (hP : P b=n b*(2*h b+1)+T b)
--       (hn : ∀j<b,0<n j) (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j))
--       (hMotif : ∀j≤b,24*2^s≤T j) (hroot : 4*(n b+1)≤T b)
--       (A B : FiniteLaw Leaf) (g : Leaf → List Bool) (Z : Leaf → ℝ)
--       (hden : ∀a,B.mass a=A.mass a*(1+Z a)) (hZ : ∀a,0≤1+Z a)
--       (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
--       (ω a η L : ℝ) (ha : 0<a) (hL : 0<L) (hω : ω∈Set.Ioo 0 1)
--       (hov : ∀j<b+1,ω≤listTraceOverlap q hq
--         (pureAtomRun (sourceBlockWord s P atom j false) (h j))
--         (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
--       (hk : 1≤k) (hMoment : A.expect (fun a => |Z a|^(2*k))≤L^(2*k))
--       (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2)
--       (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
--       (herror : sourceClippingCost T n s b k ω a L≤1/2) :
--       Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
--         (sourceBlockWord s P atom (b+1) true) k
--         (sourceClippingCost T n s b k ω a L+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1))
--         (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.ApproximatesTrace`, `OAI.TraceReconstruction.FiniteLaw`, `OAI.TraceReconstruction.OracleTracePair`, `OAI.TraceReconstruction.SourceLayoutMargins`, `OAI.TraceReconstruction.SourceLeafCount`, `OAI.TraceReconstruction.hiddenSmoothingBound`, `OAI.TraceReconstruction.listTraceOverlap`, `OAI.TraceReconstruction.pureAtomRun`, `OAI.TraceReconstruction.sourceBlockWord`, `OAI.TraceReconstruction.sourceSparseCount` and `OAI.TraceReconstruction.FiniteLaw.expect` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceFitTail` (definitions bundle `OAIQ9Tr001` of this split); `OAI.TraceReconstruction.sourceClippingCost` and `OAI.TraceReconstruction.sourceSharpEnergyBudget` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proofs of `OAI.TraceReconstruction.actual_one_window_oracle` and `OAI.TraceReconstruction.source_all_levels_eventually` of this split import it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean (declaration OAI.TraceReconstruction.actual_source_oracle)

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

theorem actual_source_oracle {Leaf : Type} [Fintype Leaf]
    {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b R k : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hTpos : ∀j,0<T j) (hP : P b=n b*(2*h b+1)+T b)
    (hn : ∀j<b,0<n j) (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j))
    (hMotif : ∀j≤b,24*2^s≤T j) (hroot : 4*(n b+1)≤T b)
    (A B : FiniteLaw Leaf) (g : Leaf → List Bool) (Z : Leaf → ℝ)
    (hden : ∀a,B.mass a=A.mass a*(1+Z a)) (hZ : ∀a,0≤1+Z a)
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (ω a η L : ℝ) (ha : 0<a) (hL : 0<L) (hω : ω∈Set.Ioo 0 1)
    (hov : ∀j<b+1,ω≤listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
    (hk : 1≤k) (hMoment : A.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (herror : sourceClippingCost T n s b k ω a L≤1/2) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (sourceClippingCost T n s b k ω a L+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1))
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
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
end
end
end

end OAI
end
