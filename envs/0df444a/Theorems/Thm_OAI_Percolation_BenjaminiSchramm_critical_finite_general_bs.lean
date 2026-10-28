-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_finite_general_bs
-- name    : OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:18:38.568028+00:00
-- url     : https://prove2.me/theorems/d74ce3fe-c7d8-49ff-ac00-d2dfc0c6a705
-- title:
--   OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.critical_finite_general` of [lean/OAI/Probability/BenjaminiSchramm/GeneralCriticalFiniteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/GeneralCriticalFiniteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open MeasureTheory`):
--
--   ```lean
--   theorem critical_finite_general_bs [Infinite V]
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (hpc : pc G < 1) (x : V) :
--       ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.cluster`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs`, `OAI.Percolation.BenjaminiSchramm.critical_ceiling_zero_band_profile_bs`, `OAI.Percolation.BenjaminiSchramm.critical_endpoint_fractional_profiles_bs`, `OAI.Percolation.BenjaminiSchramm.critical_fullspace_threeQuarter_profiles_bs`, `OAI.Percolation.BenjaminiSchramm.critical_halfspace_fractional_profiles_bs`, `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs`, `OAI.Percolation.BenjaminiSchramm.critical_peak_comparison_at_rate_bs`, `OAI.Percolation.BenjaminiSchramm.critical_slab_fractional_of_peak_survival_bs`, `OAI.Percolation.BenjaminiSchramm.full_application_gap_bs`, `OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs` and `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/GeneralCriticalFiniteness.lean (declaration OAI.Percolation.BenjaminiSchramm.critical_finite_general)

import Mathlib
import Definitions.Def_BenjaminiSchramm

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem critical_finite_general_bs [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc : pc G < 1) (x : V) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
end
