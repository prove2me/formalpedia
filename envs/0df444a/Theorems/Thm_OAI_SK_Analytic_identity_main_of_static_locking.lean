-- Prove2me | Theorems.Thm_OAI_SK_Analytic_identity_main_of_static_locking
-- name    : OAI.SK.Analytic.identity_main_of_static_locking
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:53:02.604023+00:00
-- url     : https://prove2.me/theorems/126f29e5-f2bf-4ac9-9c7d-81ef857596d8
-- title:
--   OAI.SK.Analytic.identity_main_of_static_locking: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.identity_main_of_static_locking` of [lean/OAI/Probability/SKBarriers/SKBarriers/Dynamics/IdentityMain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Dynamics/IdentityMain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Topology`, `open Classical MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--    theorem identity_main_of_static_locking (β : ℝ) (μ : ProbabilityMeasure ℝ) {t b b' q : ℝ}
--       (ht : 0<t) (hb : 0<b) (hpack : 3*t<b^2/2) (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q)
--       (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0 < c ∧ ∃C : (n : ℕ) → Set (Disorder n),
--         (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
--         ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
--           finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
--       (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
--       Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.overlap` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.finiteMass`, `OAI.SK.Analytic.levelLogScale` and `OAI.SK.Analytic.levelRho` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.lockingUnion` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.replicaGibbsMass` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Config`, `OAI.SK.Disorder`, `OAI.SK.Edge`, `OAI.SK.continuousBadMass`, `OAI.SK.discreteBadMass`, `OAI.SK.disorderLaw` and `OAI.SK.gibbs` (the published bundle `Def_SKBarriers`).
--
--   **Used by.** The proof of `OAI.SK.main` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Dynamics/IdentityMain.lean (declaration OAI.SK.Analytic.identity_main_of_static_locking)

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S002
import Definitions.Def_OAIQ036S003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem identity_main_of_static_locking (β : ℝ) (μ : ProbabilityMeasure ℝ) {t b b' q : ℝ}
    (ht : 0<t) (hb : 0<b) (hpack : 3*t<b^2/2) (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q)
    (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0 < c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
    (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  sorry

end SK.Analytic

end
end

end OAI
end
