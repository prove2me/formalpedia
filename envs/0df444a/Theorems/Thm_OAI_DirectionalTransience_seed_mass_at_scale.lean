-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_seed_mass_at_scale
-- name    : OAI.DirectionalTransience.seed_mass_at_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:48.645176+00:00
-- url     : https://prove2.me/theorems/6f2a758d-d214-41e0-b05c-c60e1d435ffc
-- title:
--   OAI.DirectionalTransience.seed_mass_at_scale: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.seed_mass_at_scale` of [lean/OAI/Probability/Ballisticity/Coupling/SeedUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/SeedUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem seed_mass_at_scale {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
--       ∃ C c₀ g₀ R : ℝ, 0<C ∧ 0 < c₀ ∧ 0<g₀ ∧ 0<R ∧
--       ∀ r : ℝ, R ≤ r → ∀ H : ℕ,
--         (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) r →
--         ∀ π : ProbabilityMeasure (Fin k → Lattice d),
--           1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤
--             rawTupleMixture (realPosition (step e)) H π.toMeasure ω {v | TupleSeparated f (c₀*r) v}}
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.TupleSeparated`, `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.rawTupleMixture` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.separated_seeds` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/SeedUniform.lean (declaration OAI.DirectionalTransience.seed_mass_at_scale)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal000

section

attribute [-instance] _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem seed_mass_at_scale {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ R : ℝ, 0<C ∧ 0 < c₀ ∧ 0<g₀ ∧ 0<R ∧
    ∀ r : ℝ, R ≤ r → ∀ H : ℕ,
      (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      ∀ π : ProbabilityMeasure (Fin k → Lattice d),
        1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤
          rawTupleMixture (realPosition (step e)) H π.toMeasure ω {v | TupleSeparated f (c₀*r) v}} := by
  sorry

end DirectionalTransience

end

end OAI
end
