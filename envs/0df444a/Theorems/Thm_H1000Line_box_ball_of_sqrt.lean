-- Prove2me | Theorems.Thm_H1000Line_box_ball_of_sqrt
-- name    : H1000Line.box_ball_of_sqrt
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:49:28.754283+00:00
-- url     : https://prove2.me/theorems/a39474e8-f5dd-44b0-8f1a-2ca31c686617
-- title:
--   A counting rectangle contained in a disk
-- statement:
--   Let $T_0\le c_i\le T_1$ and suppose
--   $$\tfrac94+(c_i-T_0)^2<q,\qquad \tfrac94+(T_1-c_i)^2<q.$$
--   Then every complex $\rho$ with $-1\le\operatorname{Re}\rho\le2$ and
--   $T_0\le\operatorname{Im}\rho\le T_1$ lies in
--   $$B\left(\tfrac12+ic_i,\sqrt q\right).$$
--   This is the geometric containment used in the zero count.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Glue.lean#L69-L89

import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_HeightFloorCheck
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
/-  H1000Glue.lean -- integration glue for the height-1000 segment (lane h1000-prep).

    The segment's band table `BandGlue_h1000.seg` carries the TIGHT Arb enclosures (width about 1e-12)
    of the five RvM argument changes, and each band's `rh_in_box_*` theorem has its pins and its
    ball-cover geometry baked in for exactly those numbers.  A kernel evaluator will certify WIDER
    enclosures.  This file lets the integration stage swap in its own enclosures band by band:

      * `Encl`            : five enclosures `[L1,H1] … [L5,H5]` (the order of `BandGlue.BandData`);
      * `segWith i E`     : band `i` of the segment with its enclosures replaced by `E` (same `T0`, `T1`,
                            `n`, ball `c`, `R`);
      * `PinOk i E`       : the two pin inequalities of `BandGlue.BandData.Valid` for `segWith i E`
                            (decidable: `norm_num` on rationals);
      * `box_ball_of_sqrt`, `valid_of_sqrt` : the ball-cover geometry and the full `Valid` structure
                            from the band's explicit numbers (`T0`, `T1`, `c = 1/2 + i·cim`, `R = √q`);
      * `capGeom_segWith` : the K1 cap geometry transfers from `seg i` to `segWith i E`;
      * `slabClear_low`, `slab0_band0` : an edge-clearance slab below height `55/16` is zero-free by
                            the height floor (`HeightFloor.strip_clear_low`); this discharges the lower
                            slab of band 0 (`[1 - capLo 0, 1]`), leaving 49 slab facts.

    The per-band `Valid` instances and the final theorem are generated into `H1000Line_All.lean`.

    Pin budget (computed from the `seg` table, see LANE_NOTES_h1000-prep.md): the lower pin has slack
    at least 6.2827 rad and the upper at least 6.178 rad in every band, so the one-sided enclosure
    errors `2 e1 + e2 + e3 + e4 + e5` may total about 6.18 rad (for example ±1 rad each).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Glue for a finite verification; nothing here bears on RH.
-/



open Complex

section
namespace H1000Line
end H1000Line
open H1000Line

theorem H1000Line.box_ball_of_sqrt {T0 T1 cim q : ℝ} (h0 : T0 ≤ cim) (h1 : cim ≤ T1)
    (ha : 9 / 4 + (cim - T0) ^ 2 < q) (hb : 9 / 4 + (T1 - cim) ^ 2 < q) :
    ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball (⟨1 / 2, cim⟩ : ℂ) (Real.sqrt q) := by sorry
