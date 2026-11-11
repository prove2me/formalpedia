-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_EpisodeChainLedger_mean_episode_drops_local
-- name    : OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:13.377731+00:00
-- url     : https://prove2.me/theorems/c00d59cc-8923-40b1-be18-6944c1c84152
-- title:
--   OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local` of [lean/OAI/Probability/Ballisticity/Stationary/EpisodeMeanDrop.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/EpisodeMeanDrop.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.EpisodeChainLedger`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Classical`):
--
--   ```lean
--   theorem mean_episode_drops_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 < b) (hs : 0 < sfloor)
--       (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
--       (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
--       (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
--       (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u)
--       (β : ℝ) (hbad : ∀ᵐ ω ∂Q, β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal)
--       (hstages : 2*b*(∫ ω, (J ω N:ℝ) ∂Q) ≤ β/4*Real.log (N:ℝ))
--       (L : ℕ) (hL : 0<L)
--       (hcharge : ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) ≤ 2*b*L) :
--       (3*β/4*Real.log (N:ℝ) ≤
--         ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(∫ ω, (M ω N:ℝ) ∂Q)) ∧
--       ((∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1) ∧
--       (β/2*Real.log (N:ℝ) ≤ ∫ ω, ∑ i ∈ Finset.range N, if j ω i ≤ L then c ω i else 0 ∂Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.crossingQuenched`, `OAI.DirectionalTransience.episodeStageH` and `OAI.DirectionalTransience.BoundedInjection.injectionMultiplier` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.StageRadiusOrder` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.EpisodeChainLedger.dropMark`, `OAI.DirectionalTransience.EpisodeChainLedger.number`, `OAI.DirectionalTransience.EpisodeChainLedger.stepMark` and `OAI.DirectionalTransience.EpisodeChainLedger.steps` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/EpisodeMeanDrop.lean (declaration OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local)

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

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

theorem mean_episode_drops_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 < b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u)
    (β : ℝ) (hbad : ∀ᵐ ω ∂Q, β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal)
    (hstages : 2*b*(∫ ω, (J ω N:ℝ) ∂Q) ≤ β/4*Real.log (N:ℝ))
    (L : ℕ) (hL : 0<L)
    (hcharge : ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) ≤ 2*b*L) :
    (3*β/4*Real.log (N:ℝ) ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(∫ ω, (M ω N:ℝ) ∂Q)) ∧
    ((∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1) ∧
    (β/2*Real.log (N:ℝ) ≤ ∫ ω, ∑ i ∈ Finset.range N, if j ω i ≤ L then c ω i else 0 ∂Q) := by
  sorry

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end
