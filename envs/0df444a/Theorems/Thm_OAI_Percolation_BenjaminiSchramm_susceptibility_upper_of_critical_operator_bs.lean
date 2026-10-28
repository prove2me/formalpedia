-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_susceptibility_upper_of_critical_operator_bs
-- name    : OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:19:25.805668+00:00
-- url     : https://prove2.me/theorems/3d37cc6a-5e0e-4677-8cdc-2bfee81effdb
-- title:
--   OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator` of [lean/OAI/Probability/BenjaminiSchramm/OperatorSusceptibility.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/OperatorSusceptibility.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem susceptibility_upper_of_critical_operator_bs
--       [Countable V] [Countable E] [Nonempty V]
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
--       ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
--         susceptibility G p x ≤ A / ((pc G : ℝ) - p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.hV`, `OAI.Percolation.pc` and `OAI.Percolation.susceptibility` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.BenjaminiSchramm.criticalRadiiInput_of_nonamenable_bs` and `OAI.Percolation.BenjaminiSchramm.critical_volume_upper_of_operator_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/OperatorSusceptibility.lean (declaration OAI.Percolation.BenjaminiSchramm.susceptibility_upper_of_critical_operator)

import Mathlib
import Definitions.Def_BenjaminiSchramm

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem susceptibility_upper_of_critical_operator_bs
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p) := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
end
