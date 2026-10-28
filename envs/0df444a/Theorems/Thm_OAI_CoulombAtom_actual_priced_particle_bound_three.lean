-- Prove2me | Theorems.Thm_OAI_CoulombAtom_actual_priced_particle_bound_three
-- name    : OAI.CoulombAtom.actual_priced_particle_bound_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:00:45.859982+00:00
-- url     : https://prove2.me/theorems/b664811e-7651-4821-83fb-4ca1bd8775bc
-- title:
--   OAI.CoulombAtom.actual_priced_particle_bound_three: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.actual_priced_particle_bound_three` of [lean/OAI/Analysis/CoulombIonization/Variational/ActualSectorPlateau.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/ActualSectorPlateau.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem actual_priced_particle_bound_three (Z : ℕ) (hZ : 1 ≤ Z)
--       {lam : ℝ} (hlam : 0 < lam) {N : ℕ}
--       (hN : PriceMinimizes (energy Z) lam N) : N ≤ 3*Z
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually`, `OAI_CoulombBarrier_own_state_initial_barrier` and `OAI.CoulombBarrier.tail_initial_good_event` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/ActualSectorPlateau.lean (declaration OAI.CoulombAtom.actual_priced_particle_bound_three)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
attribute [local irreducible] formEnergy energy

theorem actual_priced_particle_bound_three (Z : ℕ) (hZ : 1 ≤ Z)
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) : N ≤ 3*Z := by
  sorry

end CoulombAtom

end

end OAI
end
