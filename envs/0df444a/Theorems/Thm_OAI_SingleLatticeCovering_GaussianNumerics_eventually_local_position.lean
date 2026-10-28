-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_GaussianNumerics_eventually_local_position
-- name    : OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:45:49.635207+00:00
-- url     : https://prove2.me/theorems/d67bc4a6-a2be-4734-89a5-ff5df776899e
-- title:
--   OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position` of [lean/OAI/Geometry/LatticeCovering/GaussianRates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/GaussianRates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.GaussianNumerics`, with `open MeasureTheory Filter Set GaussianDensity GaussianProjection CanonicalDensity`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem eventually_local_position : ∀ᶠ l : ℕ in atTop,
--       ∀ m D : ℕ, D ≤ l → 0 < m+D →
--         Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
--         ∀ K : Set (E (m+D)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
--           ∃ e : E (m+D) ≃ᵃ[ℝ] ((Fin m → ℝ) × E D),
--             ∀ y : E D, ‖y‖ ≤ 6*(l:ℝ)^2 → density (1/2) y/2 ≤ canonical (e '' K) y
--   ```
--
--   **Definitions.** The statement is written with `OAI.SingleLatticeCovering.CanonicalDensity.canonical`, `OAI.SingleLatticeCovering.GaussianDensity.E`, `OAI.SingleLatticeCovering.GaussianDensity.density` and `OAI.SingleLatticeCovering.Isotropization.E` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/GaussianRates.lean (declaration OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter Set GaussianDensity GaussianProjection CanonicalDensity
open scoped Topology ENNReal

theorem eventually_local_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (E (m+D)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : E (m+D) ≃ᵃ[ℝ] ((Fin m → ℝ) × E D),
          ∀ y : E D, ‖y‖ ≤ 6*(l:ℝ)^2 → density (1/2) y/2 ≤ canonical (e '' K) y := by
  sorry

end SingleLatticeCovering.GaussianNumerics

end

end OAI
end
