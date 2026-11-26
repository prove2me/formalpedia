-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_canonical
-- name    : Malliavin.naturalMartingaleRepresentation_iff_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:30.641602+00:00
-- url     : https://prove2.me/theorems/0ab03255-1318-453f-8c7a-aa1fc65e8181
-- title:
--   Malliavin: natural Martingale Representation iff canonical
-- statement:
--   Martingale representation holds exactly when the canonical best-integrand formula reconstructs
--   every terminal variable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L403-L414
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L403-L414

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.naturalMartingaleRepresentation_iff_canonical
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      ∀ G : RandomL2 P,
        G = expectationL2 G + naturalItoIntegral hB hsm hnat
          (bestNaturalItoIntegrandOfRandom hB hsm hnat G) := by sorry
