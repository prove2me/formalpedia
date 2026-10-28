-- Prove2me | Theorems.Thm_H1000Line_lnBox_sound
-- name    : H1000Line.lnBox_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:13.115373+00:00
-- url     : https://prove2.me/theorems/a8144239-4eba-4206-a076-a44f4072c61e
-- title:
--   Integer interval for a logarithm
-- statement:
--   Let $a,b,n\in\mathbb N$ with $b>0$ and $2a<b$. If $(L,H)$ is the defined
--   integer interval $\operatorname{lnBox}(a,b,n)$, then
--   $$L\le-2^{64}\log(1-a/b)\le H.$$
--   The quotient and logarithm are real; the endpoints are cast from integers.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Phase.lean#L118-L187

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
/-  H1000Phase.lean -- the Riemann-Siegel phase at a rational height, as kernel-checkable integer
    bounds (lane h1000-prep; consumed by `H1000Line`).

    For `t = tn / 2^tq` and the branch limit `Λ = lim imLnVal (1/4) (t/2)` (the one
    `KernelGammaEnvelope.gLine_decomp_explicit` exposes), `phase_sound` gives

        phaseLo tn tq k nl ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi tn tq k nl,

    where `phaseLo`, `phaseHi` are plain `Int`/`Nat` computations (the kernel evaluates them) of the
    height-uniform bracket `RSTheta.theta_bracket`:
        thetaS t - 1/(2t) ≤ Λ - (t/2) log π ≤ thetaS t,
        thetaS t = (t/4) log (1/16 + t²/4) - (1/4) arctan (2t) - t/2 - (t/2) log π.
    Ingredients: `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`, `A = 4^tq + 4 tn²`
    (`log_inner_eq`); the fixed-point series of `-log (1 - x)` with Mathlib's geometric remainder
    `Real.abs_log_sub_add_sum_range_le` (`lnBox_sound`); `log 2`, `log π` from `RSTheta.log2_box`,
    `logpi_box`; `π` from `Real.pi_gt_d20`, `pi_lt_d20`; `arctan (2t) = π/2 - arctan w` with
    `w - w³/3 ≤ arctan w ≤ w` (`ArctanTaylor`).  Every rounding is outward (`fdiv`, `cdiv`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Elementary enclosures of one special-function value; nothing here
    bears on the Riemann Hypothesis.
-/






open Real Filter Topology
open ArbEcon ArbEcon.OrderK

section
namespace H1000Line
end H1000Line
open H1000Line

noncomputable section

/-! ## A. Floor and ceiling division of an integer by a positive natural. -/









/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/

theorem H1000Line.lnBox_sound (a b nl : ℕ) (hb : 0 < b) (h2 : 2 * a < b) :
    (((lnBox a b nl).1 : ℤ) : ℝ) ≤ -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ∧
    -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ≤ (((lnBox a b nl).2 : ℤ) : ℝ) := by sorry
