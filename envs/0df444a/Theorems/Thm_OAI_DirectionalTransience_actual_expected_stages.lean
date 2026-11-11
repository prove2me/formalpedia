-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_expected_stages
-- name    : OAI.DirectionalTransience.actual_expected_stages
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:54.139459+00:00
-- url     : https://prove2.me/theorems/dc855da2-afb8-494c-9666-a51a251358d2
-- title:
--   OAI.DirectionalTransience.actual_expected_stages: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_expected_stages` of [lean/OAI/Probability/Ballisticity/Stationary/EpisodePotentialIteration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/EpisodePotentialIteration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory InformationTheory`, `open scoped ENNReal Classical`):
--
--   ```lean
--   theorem actual_expected_stages {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
--       (fexp g χ b sfloor K D β : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
--       (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
--       (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b) (hK : 0 < K) (hD : 0 ≤ D)
--       (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ))
--       (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
--         environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
--           (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
--           (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
--       (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
--       (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal (D*Real.log (N:ℝ)))
--       (hc : 1/g+(1+fexp/g)*D/K ≤ β/32)
--       (hsmall : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
--       (hlarge : 32*b ≤ β*Real.log (N:ℝ)) :
--       2*b*(∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ) ∂Q) ≤
--         β/4*Real.log (N:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.BudgetProfile`, `OAI.DirectionalTransience.TupleAtHeight`, `OAI.DirectionalTransience.TupleSeparated` and `OAI.DirectionalTransience.episodeStageH` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.stageBadEvent` and `OAI.DirectionalTransience.EpisodeChainLedger.steps` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks`, `OAI.DirectionalTransience.OperationalConstants.bad_dropMarkCut_upper`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment` and `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/EpisodePotentialIteration.lean (declaration OAI.DirectionalTransience.actual_expected_stages)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002

section

attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem actual_expected_stages {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K D β : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b) (hK : 0 < K) (hD : 0 ≤ D)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ))
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal (D*Real.log (N:ℝ)))
    (hc : 1/g+(1+fexp/g)*D/K ≤ β/32)
    (hsmall : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
    (hlarge : 32*b ≤ β*Real.log (N:ℝ)) :
    2*b*(∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ) ∂Q) ≤
      β/4*Real.log (N:ℝ) := by
  sorry

end DirectionalTransience

end

end OAI
end
