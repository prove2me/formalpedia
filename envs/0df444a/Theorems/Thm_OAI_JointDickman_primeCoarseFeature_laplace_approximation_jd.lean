-- Prove2me | Theorems.Thm_OAI_JointDickman_primeCoarseFeature_laplace_approximation_jd
-- name    : OAI.JointDickman.primeCoarseFeature_laplace_approximation_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:14.89989+00:00
-- url     : https://prove2.me/theorems/9d22cbca-4ffd-42b3-b876-1b215f23274b
-- title:
--   OAI.JointDickman.primeCoarseFeature_laplace_approximation_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.primeCoarseFeature_laplace_approximation` of [lean/OAI/NumberTheory/JointDickman/Analysis/CoarseLaplaceApproximation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CoarseLaplaceApproximation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem primeCoarseFeature_laplace_approximation_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {m : ℕ} (hm : 0 < m) (d : Fin m) {ε : ℝ} (hε : 0 < ε) :
--       ∃ P : Polynomial ℝ, ∀ᶠ B : ℕ in atTop,
--         (∑ x, fullPrimeMass (auxiliaryPrimes B) x*
--           (primeCoarseFeature m B d x-
--             ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)^2) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.fullPrimeMass`, `OAI.JointDickman.primeCoarseFeature`, `OAI.JointDickman.primeLaplaceFeature`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Analysis/CoarseLaplaceApproximation.lean (declaration OAI.JointDickman.primeCoarseFeature_laplace_approximation)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem primeCoarseFeature_laplace_approximation_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {m : ℕ} (hm : 0 < m) (d : Fin m) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ᶠ B : ℕ in atTop,
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x*
        (primeCoarseFeature m B d x-
          ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)^2) < ε := by
  sorry

end JointDickman

end OAI
end
