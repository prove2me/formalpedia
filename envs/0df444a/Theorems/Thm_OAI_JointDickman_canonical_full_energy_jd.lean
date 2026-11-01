-- Prove2me | Theorems.Thm_OAI_JointDickman_canonical_full_energy_jd
-- name    : OAI.JointDickman.canonical_full_energy_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:24:03.825522+00:00
-- url     : https://prove2.me/theorems/cf849cc2-29dc-4ae1-aa1d-a524d3880cbc
-- title:
--   OAI.JointDickman.canonical_full_energy_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.canonical_full_energy` of [lean/OAI/NumberTheory/JointDickman/Counting/CanonicalFullEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CanonicalFullEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset MeasureTheory TwoPointCorrelations`, `open scoped Classical`):
--
--   ```lean
--   theorem canonical_full_energy_jd {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
--       (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
--       (hη : 0 < η) (hη' : η ≤ 1/12)
--       (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
--       (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
--       (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
--       (F : ℕ → ℂ) (hF : Multiplicative F) (hb : ∀ n, ‖F n‖ ≤ 1)
--       {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
--       (hS : S ⊆ Set.Ioc (-T) T) :
--       (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
--         4*(∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
--           ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J,
--           ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
--         2*(2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η))+
--           1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹+2*(T/N+1)/P)+
--         48*Real.exp 1*(T/N+2)*
--           (((Ioc N (2*N)).filter fun n =>
--             ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card:ℝ)/N
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.angularMellinPolynomial`, `OAI.JointDickman.canonicalMellinBands`, `OAI.TwoPointCorrelations.mrtBandUpper`, `OAI.TwoPointCorrelations.mrtBaseResolution`, `OAI.JointDickman.MellinPrimeBands` and `OAI.JointDickman.MellinPrimeBands.polynomial` (definitions bundle `OAIQ083J001` of this split); `OAI.TwoPointCorrelations.Multiplicative`, `OAI.TwoPointCorrelations.mrtNoSmallBand` and `OAI.TwoPointCorrelations.mrtTypical` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.centered_bin_spectral_jd` and `OAI.JointDickman.twisted_bin_spectral_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CanonicalFullEnergy.lean (declaration OAI.JointDickman.canonical_full_energy)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem canonical_full_energy_jd {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
    (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
    (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
    (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hb : ∀ n, ‖F n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
      4*(∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
        ((canonicalMellinBands P Q η).polynomial F) (canonicalMellinBands P Q η).threshold J,
        ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
      2*(2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η))+
        1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹+2*(T/N+1)/P)+
      48*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card:ℝ)/N := by
  sorry

end JointDickman

end OAI
end
