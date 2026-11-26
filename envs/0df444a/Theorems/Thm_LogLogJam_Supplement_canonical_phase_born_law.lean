-- Prove2me | Theorems.Thm_LogLogJam_Supplement_canonical_phase_born_law
-- name    : LogLogJam.Supplement.canonical_phase_born_law
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:21:05.425739+00:00
-- url     : https://prove2.me/theorems/07893997-c4e4-51b7-b638-7420e5317b36
-- title:
--   Born distribution of the canonical even phase readout
-- statement:
--   A fixed phase POVM with the canonical even Fock matrix elements has the specified phase-amplitude density for every one-mode squeezed vacuum, including the vacuum at zero squeezing and arbitrary completions on odd sectors.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3

import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement

theorem canonical_phase_born_law (M : FockPOVM (Occupation (Fin 1)) ℝ)
    (hM : ∀ (B : Set ℝ), MeasurableSet B → ∀ i j : ℕ,
      M.effect B (fun _ => 2*i) (fun _ => 2*j) =
        (∫ x in B ∩ Set.Ico 0 (2*Real.pi), Complex.exp (Complex.I*(((i:ℝ)-j)*x))) / (2*Real.pi:ℝ))
    (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let b := fun n : ℕ => Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
    let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
    M.law ρ.coefficients B = ENNReal.ofReal ((∫ x in B ∩ Set.Ico 0 (2*Real.pi),
      ‖∑' n, (((b n / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * z^n) * Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2) / (2 * Real.pi)) := by sorry

end LogLogJam.Supplement
