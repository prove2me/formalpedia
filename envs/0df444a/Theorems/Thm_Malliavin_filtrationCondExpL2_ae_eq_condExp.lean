-- Prove2me | Theorems.Thm_Malliavin_filtrationCondExpL2_ae_eq_condExp
-- name    : Malliavin.filtrationCondExpL2_ae_eq_condExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:36.466153+00:00
-- url     : https://prove2.me/theorems/a950a62a-6bb3-4334-acc7-a0110fac6eab
-- title:
--   Malliavin: filtration Cond Exp L2 ae eq cond Exp
-- statement:
--   The ambient representative of `filtrationCondExpL2` agrees almost everywhere with
--   Mathlib's function-valued conditional expectation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L320-L325
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L320-L325

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.filtrationCondExpL2_ae_eq_condExp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P] P[(F : W → ℝ) | 𝓕 t] := by sorry
