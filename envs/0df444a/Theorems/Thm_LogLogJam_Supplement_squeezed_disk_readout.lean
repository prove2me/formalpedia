-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_disk_readout
-- name    : LogLogJam.Supplement.squeezed_disk_readout
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:26:32.594544+00:00
-- url     : https://prove2.me/theorems/d340e76a-5985-5901-93e9-516e630c4d66
-- title:
--   A joint disk-valued readout for a single squeezed Fock state
-- statement:
--   A fixed single-mode POVM with two real outcomes has an explicit joint Born density for every squeezed Fock vector with disk parameter q, uniformly on the open unit disk. The Fock coefficients and the reference measure are specified in the statement.
-- source:
--   https://arxiv.org/abs/2607.12983, supporting the one-copy endpoint of Theorem 8.16

import Mathlib
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
open MeasureTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open scoped Classical ComplexConjugate ENNReal Topology

namespace LogLogJam.Supplement
theorem squeezed_disk_readout :
    ∃ M : FockPOVM (Occupation (Fin 1)) (ℝ × ℝ), ∀ (q : ℂ) (N : ℝ),
    ‖q‖ < 1 → ∀ ρ : State (Occupation (Fin 1)),
    (let ψ (i : Occupation (Fin 1)) := if Even (i 0) then
      ((N * (Real.sqrt ((i 0 / 2).centralBinom : ℝ) / 2 ^ (i 0 / 2)) : ℝ) : ℂ) * q^(i 0 / 2) else 0
     ∀ i j, ρ.coefficients i j = ψ i * conj (ψ j)) →
    ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      let arc := fun b : ℝ => ENNReal.ofReal b⁻¹ • (volume.restrict (Set.Ico 0 b))
      M.law ρ.coefficients B = ENNReal.ofReal (∫ x in B,
        ‖(N:ℂ)*(1-q*((Real.sin x.1:ℂ)*Complex.exp (-Complex.I*x.2)))⁻¹‖^2
          ∂((arc Real.pi).prod (arc (2*Real.pi)))) := by sorry
end LogLogJam.Supplement
