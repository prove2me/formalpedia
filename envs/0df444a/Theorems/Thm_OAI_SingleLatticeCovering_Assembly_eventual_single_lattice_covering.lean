-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_Assembly_eventual_single_lattice_covering
-- name    : OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:39:03.948132+00:00
-- url     : https://prove2.me/theorems/1dc51663-3a45-447c-9034-a14ece06520d
-- title:
--   OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering` of [lean/OAI/Geometry/LatticeCovering/Assembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/Assembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.Assembly`, with `open MeasureTheory`, `open Filter Topology`, `open scoped BigOperators Pointwise ENNReal`):
--
--   ```lean
--   theorem eventual_single_lattice_covering :
--       ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
--         IsCompact K → Convex ℝ K → (interior K).Nonempty →
--         ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
--           K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
--           (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ)
--   ```
--
--   **Used by.** The proof of `OAI.CoveringOrder.optimal_order` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/Assembly.lean (declaration OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SingleLatticeCovering.Assembly
open MeasureTheory
open Filter Topology
open scoped BigOperators Pointwise ENNReal

theorem eventual_single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  sorry

end SingleLatticeCovering.Assembly

end

end OAI
end
