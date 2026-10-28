-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_reference_clipped_exists
-- name    : OAI.TraceReconstruction.source_reference_clipped_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:54:26.99777+00:00
-- url     : https://prove2.me/theorems/efd004ec-bbf1-47a1-94d6-f1fdf550dc8f
-- title:
--   OAI.TraceReconstruction.source_reference_clipped_exists: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_reference_clipped_exists` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem source_reference_clipped_exists {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
--       (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
--       (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
--       (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0)
--       (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1≤k)
--       (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
--       (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
--       (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
--       (hB : ∀τ,((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
--         (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
--           (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a)
--       (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
--       Nonempty (ClippedOracle
--         ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z false)
--           (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_total T n s b M P Z hc false))
--         ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z true)
--           (sourceOracleDensity_nonneg T n s b Z hZ true) (sourceOracleDensity_total T n s b M P Z hc true))
--         k (sourceClippingCost T n s b k ω a L)
--         (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.ClippedOracle`, `OAI.TraceReconstruction.FiniteLaw`, `OAI.TraceReconstruction.PairedMechanisms`, `OAI.TraceReconstruction.Reports`, `OAI.TraceReconstruction.SourceLeafCount`, `OAI.TraceReconstruction.SourceTrialCount`, `OAI.TraceReconstruction.hiddenSmoothingBound`, `OAI.TraceReconstruction.instDecidableEqProd_solutions`, `OAI.TraceReconstruction.sourceSparseCount`, `OAI.TraceReconstruction.FiniteLaw.eventMass`, `OAI.TraceReconstruction.FiniteLaw.expect` and `OAI.TraceReconstruction.FiniteLaw.withDensity` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceFitTail` (definitions bundle `OAIQ9Tr001` of this split); `OAI.TraceReconstruction.sourceClippingCost`, `OAI.TraceReconstruction.sourceEffectiveHiddenTail`, `OAI.TraceReconstruction.sourceOracleDensity`, `OAI.TraceReconstruction.sourceOracleDensity_nonneg`, `OAI.TraceReconstruction.sourceOracleDensity_total`, `OAI.TraceReconstruction.sourceReferenceLaw`, `OAI.TraceReconstruction.sourceSharpEnergyBudget` and `OAI.TraceReconstruction.sourceTypicalSet` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.actual_source_oracle` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/SourceOracle.lean (declaration OAI.TraceReconstruction.source_reference_clipped_exists)

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
namespace TraceReconstruction
open scoped Classical

attribute [local instance] OAI.TraceReconstruction.instDecidableEqProd_solutions
theorem source_reference_clipped_exists {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0)
    (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1≤k)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (hB : ∀τ,((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
      (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
        (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
    Nonempty (ClippedOracle
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z false)
        (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_total T n s b M P Z hc false))
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z true)
        (sourceOracleDensity_nonneg T n s b Z hZ true) (sourceOracleDensity_total T n s b M P Z hc true))
      k (sourceClippingCost T n s b k ω a L)
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

end OAI
end
