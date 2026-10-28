-- Prove2me | Theorems.Thm_H1000Line_chainOk_get
-- name    : H1000Line.chainOk_get
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:38:39.168162+00:00
-- url     : https://prove2.me/theorems/f470435d-9eec-45bb-8b3a-11ef461a5773
-- title:
--   Adjacent entries of a checked sample chain
-- statement:
--   Let $P$ be a finite list of critical-line sample points whose chain checker succeeds.
--   If $i+1<|P|$, then the dyadic height of $P_i$ is strictly below that of $P_{i+1}$
--   according to the Boolean height comparator, and their claimed sign bits differ:
--   $$\operatorname{tlt}(P_i,P_{i+1})=\mathrm{true},\qquad
--   P_i.\operatorname{pos}\ne P_{i+1}.\operatorname{pos}.$$
--   This extracts the adjacent-order and alternating-sign conditions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Line.lean#L130-L146

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
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
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
/-  H1000Line.lean -- the on-line sign certificate of the height-1000 ladder segment (lane
    h1000-prep, memo ANDURIL_ARB_DISCHARGE_2026-09-23, input H1 `hLine`, brick K4 in EM form).

    THE TWO THEOREMS, PROVED ONCE.  For the Boolean checker `ptCheck p` of `H1000Point` on a point
    record `p : LinePt` (height `t = tn / 2^tq`, EM cut `N`, the two evaluator states, remainder and
    phase hints, and a CLAIMED sign):

        ptCheck_sound : ptCheck p = true →
          (p.pos = true → 0 < gLine t) ∧ (p.pos = false → gLine t < 0),

    and the band assembly `band_sound`: a list of kernel-checked points with alternating signs inside
    `[T0, T1]` (`bandOk`) gives the VERBATIM `hLine` shape of `TuringBand.BandStatement` (`n` strictly
    increasing zeros of `completedRiemannZeta` on the critical line in `[T0, T1]`), through
    `SignChain.alternating_signs_chain`.

    HOW THE SIGN IS CERTIFIED (all kernel arithmetic on `Nat`/`Int`, no hypotheses):
      * `gLine t = M(t) * S(t)`, `S = cos φ · Re ζ(1/2+it) - sin φ · Im ζ(1/2+it)`,
        `M(t) ≥ (3/4) e^{-π|t|/2} > 0`             (`KernelGammaEnvelope.gLine_decomp_explicit`,
                                                      `gammaRMag_bounds`), so sign gLine = sign S;
      * Re ζ, Im ζ : the order-13 Euler-Maclaurin ball (`EMZetaHighEval.zeta_ballK`,
        `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the Dirichlet sum by the ArbEconomics Nat
        evaluator (`ArbEcon.chunk_sound`, `EMZetaHighCheck.valid64`)       [H1000Point.zball_sound];
      * φ = Λ - (t/2) log π : the height-uniform bracket `RSTheta.theta_bracket` evaluated in integers
                                                                        [H1000Phase.phase_sound];
      * cos φ, sin φ : the evaluator's own `ArbEcon.trig` after a `2π m` shift [H1000Point.trig_phase];
      * the product ball `|S · 2^64 · W - sCtr| ≤ sRad` and the sign test   [H1000Point.s_ball].

    Because |ζ(1/2+it)| = |Z(t)| on the line, the φ uncertainty (half-width about 1/(4t)) enters
    only relatively: the certified interval is about Z(t)(1 ± √2/(4t)), plus the absolute EM error.

    The 25 band instances of `BandGlue_h1000.seg` are generated by
    `telperion/examples/zeta_reflection/emit_h1000_line.py` (modules `H1000Line_B00 … B24`,
    assembled in `H1000Line_All`).

    KERNEL FOOTGUN (see `ptCheck_spec`): never make the kernel decide a definitional equality between
    `cond`/`decide` forms on a symbolic point; extract conjuncts by rewriting with lemmas.

    Trust: axioms [propext, Classical.choice, Quot.sound] (see AxiomGuardH1000Line.lean); no
    `sorry`, no `native_decide`, every numeric fact is decided by the kernel (`decide +kernel`).

    conjecture1_proved = False.  Finite interval arithmetic and the intermediate value theorem at
    finitely many heights; nothing here bears on the Riemann Hypothesis.
-/


open Real Filter Topology
open ArbEcon ArbEcon.OrderK

section
namespace H1000Line
end H1000Line
open H1000Line

noncomputable section







/-! ## H. Bands: a list of kernel-checked points gives the `hLine` shape. -/

theorem H1000Line.chainOk_get : ∀ (ps : List LinePt), chainOk ps = true →
    ∀ (i : ℕ) (h : i + 1 < ps.length),
      tlt (ps[i]'(by omega)) ps[i + 1] = true ∧ (ps[i]'(by omega)).pos ≠ ps[i + 1].pos
  := by sorry
