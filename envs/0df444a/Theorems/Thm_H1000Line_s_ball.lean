-- Prove2me | Theorems.Thm_H1000Line_s_ball
-- name    : H1000Line.s_ball
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:32.16577+00:00
-- url     : https://prove2.me/theorems/262cb8a0-9a0f-4a20-baa3-161fcec9aeb2
-- title:
--   Enclosure for the rotated real part of zeta
-- statement:
--   Let $p$ be critical-line point data, $\Lambda\in\mathbb R$, and
--   $\phi=\operatorname{phiOf}(p,\Lambda)$. Suppose the defined signed trig data
--   enclose $2^{64}\cos\phi$ and $2^{64}\sin\phi$, and the defined zeta data
--   enclose $W\operatorname{Re}\zeta(1/2+it)$ and
--   $W\operatorname{Im}\zeta(1/2+it)$, where $W=zW(p)$ and $t=t(p)$. Then
--   $$\left|2^{64}W\bigl(\cos\phi\,\operatorname{Re}\zeta(1/2+it)
--   -\sin\phi\,\operatorname{Im}\zeta(1/2+it)\bigr)-\operatorname{sCtr}(p)\right|
--   \le\operatorname{sRad}(p).$$
--   This supplies the signed enclosure used to detect an on-line zero.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Point.lean#L260-L296

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
/-  H1000Point.lean -- the point record and the pieces of the on-line sign certificate (lane
    h1000-prep; consumed by `H1000Line`).

    `LinePt` (height `t = tn / 2^tq`, EM cut, evaluator states, remainder and phase hints, claimed
    sign) and the kernel-evaluable pieces of `ptCheck`: the Dirichlet chunks `dirOk`
    (`ArbEcon.chunk_sound`), the integer zeta ball `zcX, zrX, zcY, zrY` at scale `zW`
    (`zball_sound`, from `EMZetaHighEval.zeta_ballK`, `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the
    shifted phase interval `thLo, thHi` and its `trig` (`trig_phase`, from `H1000Phase.phase_sound` and
    `ArbEcon.trig_sound`), the product ball `sCtr ± sRad` of `S · 2^64 · W` (`s_ball`), and the
    positive magnitude factor of `gLine` (`gLine_eq_mag_mul`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.
-/



open Real Filter Topology
open ArbEcon ArbEcon.OrderK

section
namespace H1000Line
end H1000Line
open H1000Line

noncomputable section

/-! ## E. The point record, the Dirichlet chunks and the integer zeta ball. -/



























/-! ## F. The product ball and the sign test. -/

theorem H1000Line.s_ball (p : LinePt) (Λ : ℝ)
    (hc : |Real.cos (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).cs * ((trigP p).cm : ℝ)| ≤ ((trigP p).cr : ℝ))
    (hsn : |Real.sin (phiOf p Λ) * 2 ^ 64 - sgn (trigP p).ss * ((trigP p).sm : ℝ)| ≤ ((trigP p).sr : ℝ))
    (hX : |(riemannZeta (sOf (tOf p))).re * (zW p : ℝ) - (zcX p : ℝ)| ≤ (zrX p : ℝ))
    (hY : |(riemannZeta (sOf (tOf p))).im * (zW p : ℝ) - (zcY p : ℝ)| ≤ (zrY p : ℝ)) :
    |(Real.cos (phiOf p Λ) * (riemannZeta (sOf (tOf p))).re
        - Real.sin (phiOf p Λ) * (riemannZeta (sOf (tOf p))).im) * 2 ^ 64 * (zW p : ℝ)
      - (sCtr p : ℝ)| ≤ (sRad p : ℝ) := by sorry
