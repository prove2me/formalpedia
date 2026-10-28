-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_root_quarterGhost_differential_bs
-- name    : OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:11.366601+00:00
-- url     : https://prove2.me/theorems/c8f96061-ad01-414b-a38b-40f1d99c96ff
-- title:
--   OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential` of [lean/OAI/Probability/BenjaminiSchramm/GhostMomentDischarge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/GhostMomentDischarge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open Set MeasureTheory`, `open scoped Classical ENNReal NNReal BigOperators`):
--
--   ```lean
--   theorem root_quarterGhost_differential_bs
--       (hinj : Function.Injective G)
--       (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
--       (hq : (criticalModel G).QuasiTransitive)
--       (p : unitInterval) (hp : (p : ℝ) < 1)
--       (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
--       (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
--         (criticalModel G).quarterThreeQuarterMoment p x < ⊤) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
--         (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
--           (criticalModel G).quarterGhostMagnetization p x (t^4)) ≤
--         C*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
--           (criticalModel G).quarterGhostMagnetization p x (t^4))^2 +
--         t^4*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
--           (criticalModel G).quarterGhostDerivative p x (t^4)) +
--         C*t^6*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
--           (criticalModel G).quarterGhostDerivative p x (t^4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.orbitRepresentatives`, `OAI.CriticalPercolation.BondGraph.quarterGhostDerivative`, `OAI.CriticalPercolation.BondGraph.quarterGhostMagnetization`, `OAI.CriticalPercolation.BondGraph.quarterThreeQuarterMoment` and `OAI.CriticalPercolation.BondGraph.OrbitRepresentatives` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.criticalModel` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.cluster` and `OAI.Percolation.law` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.subdivision_gap_input_proved_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/GhostMomentDischarge.lean (declaration OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_quarterGhost_differential_bs
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
      (criticalModel G).quarterThreeQuarterMoment p x < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4)) ≤
      C*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4))^2 +
      t^4*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) +
      C*t^6*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) := by
  sorry

end Percolation.BenjaminiSchramm

end

end OAI
end
