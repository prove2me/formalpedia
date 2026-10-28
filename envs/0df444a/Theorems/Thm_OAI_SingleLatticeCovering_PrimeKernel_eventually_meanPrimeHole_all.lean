-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_PrimeKernel_eventually_meanPrimeHole_all
-- name    : OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:46:09.328989+00:00
-- url     : https://prove2.me/theorems/12cbfa80-7629-432b-bbc3-c3cdbc701def
-- title:
--   OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all` of [lean/OAI/Geometry/LatticeCovering/MeanHoles.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/MeanHoles.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.PrimeKernel`, with `open MeasureTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open Module Submodule MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung`, `open scoped Pointwise ENNReal BigOperators`):
--
--   ```lean
--   theorem eventually_meanPrimeHole_all (hd : 270 ≤ n+1)
--       {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
--       (hVeta : volume.real J ≤ sourceEta (n+1)) :
--       ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
--         meanPrimeHole J p ≤ Real.exp (-volume.real J)+301*Real.exp (-sourceEta (n+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SingleLatticeCovering.PrimeKernel.meanPrimeHole` (definitions bundle `OAIQ16Cd000` of this split); `OAI.SingleLatticeCovering.SimplexYoung.sourceEta` (definitions bundle `OAIQ16Cd001` of this split).
--
--   **Used by.** The proof of `OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/MeanHoles.lean (declaration OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all)

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Definitions.Def_OAIQ16Cd001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
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
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology Horizontal ConvexGrid SimplexYoung
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

theorem eventually_meanPrimeHole_all (hd : 270 ≤ n+1)
    {J : Set (Fin (n+1) → ℝ)} (hJ : IsCompact J) (hconv : Convex ℝ J)
    (hVeta : volume.real J ≤ sourceEta (n+1)) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      meanPrimeHole J p ≤ Real.exp (-volume.real J)+301*Real.exp (-sourceEta (n+1)) := by
  sorry

end SingleLatticeCovering.PrimeKernel

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
end
end
end
end
end
end

end OAI
end
