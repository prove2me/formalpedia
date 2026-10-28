-- Prove2me | Theorems.Thm_H11K_boxCert_of_parts_sharp
-- name    : H11K.boxCert_of_parts_sharp
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:26:02.661144+00:00
-- url     : https://prove2.me/theorems/fe1f54a3-f3ec-4241-9051-0341c38e0e24
-- title:
--   A box certificate from sharp band components
-- statement:
--   Let $d$ be band data with $d.T_0\le\ell$ and $h\le d.T_1$, and let $E$ be its
--   argument enclosure. Suppose the sharp validity and cap-geometry conditions hold;
--   the band has its required on-line zero list; the lower and upper adjoining slabs
--   are zero-free; the gamma-side bounds hold; and both horizontal zeta changes lie in
--   their recorded intervals. Then
--   $$\operatorname{BoxCert}\!\left(\tfrac1{4000000},\tfrac{3999999}{4000000},\ell,h\right).$$
--   Here $\operatorname{BoxCert}$ is the existential band statement together with its
--   line-list and analytic input conditions, as defined by the certificate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_Turing.lean#L265-L276

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Line
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgChangeGlue
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
import Definitions.Def_ArdaRH65K_Turing121_HeightFloorCheck
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArgGammaR_argChangeVert_gammaR_neg_one_eq
import Theorems.Thm_ArgGammaR_argChangeVert_gammaR_two_eq
import Theorems.Thm_ArgZetaTwo_argChangeVert_zeta_two_eq
import Theorems.Thm_ArgZetaTwo_log_pi_sq_div_six_lt
import Theorems.Thm_ArgZetaTwo_log_zeta_two_eq
import Theorems.Thm_ArgZetaTwo_norm_primeLog_le
import Theorems.Thm_ArgZetaTwo_primeLog_two
import Theorems.Thm_EdgeClearGlue_hins_of_slabClear
import Theorems.Thm_H11K_stmt_of_validS
import Theorems.Thm_RSDesignTheta_lam_bracket
import Theorems.Thm_ThetaConverge_imLnVal_cauchy
import Theorems.Thm_ZetaZeroConfinement_zeta_zero_iff_completed_zero_of_im_ne
namespace Arb4
end Arb4
namespace Arb4.Q
end Arb4.Q
namespace BandGlue
end BandGlue
namespace BandGlue.BandData
end BandGlue.BandData
namespace RSDesignTheta
end RSDesignTheta
namespace ThetaGap
end ThetaGap
/-  H11K_Turing.lean -- lane H11K: the Turing band template with SHARP pi pins, for WIDE bands.

    `TuringBand.band_count_eq` pins the band count with `3.14 < π < 3.1416`.  The upper pin
    `2 H1 + H2 - L3 + H4 + H5 < 2 * 3.14 * (N + 1)` then loses `2 (π - 3.14) N ≈ 0.0032 N` radians,
    which (with the K6a range `[-249/250, 249/250]` alone costing about 4 radians) caps a band at
    roughly 700 zeros.  A single band over `[31851/4, 11004]` holds 3541 zeros.  This file re-proves
    the same template with `3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`); the RvM
    edge decomposition (`DiffractionCore.zero_count_band_edge_decomp`), the Blaschke split and the
    count-exhaustion core are reused unchanged.

      * `band_count_eq_sharp`, `turing_band_on_line_sharp` -- `TuringBand.band_count_eq` /
        `turing_band_on_line` with the sharp pins (proofs copied, constants changed);
      * `ValidS`, `stmt_of_validS` -- `BandGlue.BandData.Valid` / `stmt_of_valid` with the sharp
        pins; the conclusion is the band's canonical statement `d.Stmt σ0 σ1` (the same Prop,
        `TuringBand.BandStatement`, whatever the pins), so every other piece of `BandGlue` applies;
      * `validBS`, `validS_of_B` -- the decidable side conditions as ONE Boolean (as `Arb4.validB`);
      * `boxCert_of_parts_sharp` -- `Arb4.boxCert_of_parts` with `ValidS`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


open Complex

section
namespace H11K
end H11K
open H11K





open BandGlue BandGlue.BandData







open Arb4 Arb4.Q

theorem H11K.boxCert_of_parts_sharp {lo hi δ0 δ1 : ℝ} (d : BandData) (E : EnclQ) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) (hV : ValidS (1 / 4000000) (3999999 / 4000000) (withEncl d E))
    (hG : d.CapGeom δ0 δ1) (hL : d.LineHyp) (hs0 : EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0)
    (hs1 : EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1)) (hS : ArgChangeGlue.K6Side (withEncl d E))
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc E.L2.val E.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc E.L3.val E.H3.val) :
    BoxCert (1 / 4000000) (3999999 / 4000000) lo hi := by sorry
