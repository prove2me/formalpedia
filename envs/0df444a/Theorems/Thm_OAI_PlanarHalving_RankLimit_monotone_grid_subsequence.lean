-- Prove2me | Theorems.Thm_OAI_PlanarHalving_RankLimit_monotone_grid_subsequence
-- name    : OAI.PlanarHalving.RankLimit.monotone_grid_subsequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:48:52.795855+00:00
-- url     : https://prove2.me/theorems/61fccaff-ffbd-4623-ae9c-9e5f54fdaf19
-- title:
--   Helly-type selection for coordinatewise monotone maps of the plane into [0,1]
-- statement:
--   **Statement.** Let $\iota$ be a countable type, and for each $n \in \mathbb N$ and $i \in \iota$ let $f_n^i : \mathbb R^2 \to [0,1]$ be monotone for the coordinatewise order on $\mathbb R^2$ (`Point`, from the published bundle `Def_HalvingLines`). Then there are a strictly increasing $\varphi : \mathbb N \to \mathbb N$ and functions $F^i : \mathbb R^2 \to [0,1]$ such that
--   - each $F^i$ is monotone and measurable;
--   - at every point $x$ where $F^i$ is continuous, $f_{\varphi(n)}^i(y_n) \to F^i(x)$ for every sequence $y_n \to x$.
--
--   This is a two-dimensional, countably indexed form of Helly's selection theorem. OpenAI's paper (*A power saving for planar halving lines*) uses it in Section 4 for the rank coordinates $f_C$: "Extract a subsequence on a countable dense grid, simultaneously for all $C$. The lower monotone extensions of the grid limits give Borel monotone functions $f_C$. At every continuity point $p$ of $f_C$, squeezing between grid points below and above $p$ shows convergence even along moving arguments."
--
--   Lean: `OAI.PlanarHalving.RankLimit.monotone_grid_subsequence`, OpenAI's theorem of that name. It needs only Mathlib and the published bundle `Def_HalvingLines`. It is published as a standalone result for reuse; the formal proof of `OAI.PlanarHalving.power_bounds` reaches its limits through other lemmas of the same module and does not import it.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, Section 4 ("Extract a subsequence on a countable dense grid, simultaneously for all C. The lower monotone extensions of the grid limits give Borel monotone functions"), https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Compactness.lean (declaration OAI.PlanarHalving.RankLimit.monotone_grid_subsequence)

import Mathlib
import Definitions.Def_HalvingLines

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace RankLimit

open Filter MeasureTheory Set Metric
open scoped Topology

theorem monotone_grid_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → Point → unitInterval) (hf : ∀ n i, Monotone (f n i)) :
    ∃ (φ : ℕ → ℕ) (F : ι → Point → unitInterval), StrictMono φ ∧
      (∀ i, Monotone (F i) ∧ Measurable (F i)) ∧
      (∀ i x, ContinuousAt (F i) x → ∀ y : ℕ → Point,
        Tendsto y atTop (𝓝 x) →
        Tendsto (fun n => f (φ n) i (y n)) atTop (𝓝 (F i x))) := by
  sorry

end RankLimit

end PlanarHalving

end OAI
end
