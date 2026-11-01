-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_physical_global_renormalized_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:30:05.82399+00:00
-- url     : https://prove2.me/theorems/5033769d-cf8d-4c2e-bf6c-dc820f6dfd73
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PhysicalGlobalRenormalized.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PhysicalGlobalRenormalized.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set`):
--
--   ```lean
--   theorem GlobalCollisionLimit.physical_global_renormalized_q80
--       {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
--       (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
--       (β : Renormalization) (φ : KineticTest) :
--       IntegrableOn (renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ) nonnegativeTimes ∧
--       (∫ z in nonnegativeTimes, renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ z)+
--         (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.physicalEvolution` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.kineticProfile` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.KineticTest`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Renormalization`, `OAI.BoltzmannNonuniqueness.SpaceTimePhase`, `OAI.BoltzmannNonuniqueness.Velocity`, `OAI.BoltzmannNonuniqueness.entropyMoment`, `OAI.BoltzmannNonuniqueness.maxwellian`, `OAI.BoltzmannNonuniqueness.nonnegativeTimes` and `OAI.BoltzmannNonuniqueness.renormalizedIntegrand` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.periodicExistenceInput_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PhysicalGlobalRenormalized.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_global_renormalized)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_global_renormalized_q80
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ) nonnegativeTimes ∧
    (∫ z in nonnegativeTimes, renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ z)+
      (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
