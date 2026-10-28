-- Prove2me | Theorems.Thm_H1000Oct_piece_octX_pos
-- name    : H1000Oct.piece_octX_pos
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:08:34.115089+00:00
-- url     : https://prove2.me/theorems/befef40c-4a53-4a79-9a03-d178fa022903
-- title:
--   A positive octant projection on a contour piece
-- statement:
--   Let $c,o$ be configurations with $s_c=\sigma_c+it_c$ given by
--   $\sigma_c=(o.a-o.b)/o.q$, $t_c=c.t_n/2^{c.t_q}$. Let $N\ge2$, $K,p\in\mathbb N$,
--   and let states $x_1,x_2$ satisfy the defined invariants after $N-1$ and $N$ terms.
--   Suppose $\operatorname{checkOct}$ succeeds for integer octant $j$, radius
--   $r=r_n/r_d$, and budget $F=F_n/F_d$. Let $R,L,a,U,G,E\in\mathbb R$ satisfy
--   $$r\le R,\quad x_2.\mathrm{lhi}\le2^{c.P}L,\quad RL\le1,\quad a>0,\quad
--   (a+R)^2\le(\sigma_c-1)^2+t_c^2,\quad U\ge0,$$
--   $$ (|\sigma_c|+2K-1)^2+t_c^2\le U^2,\quad
--   |n^{-s_c}|\le G\ \ (1\le n\le N),$$
--   and $|\zeta(x+it_c)-\operatorname{emFinite}(K,x+it_c,N)|\le E$ for every
--   $|x-\sigma_c|\le r$. If the defined bounds satisfy
--   $$G\bigl(C_p(RL)^{p+1}(N-1+\operatorname{emcB}(K,N,a,U))
--   +3\operatorname{corrVar}(K,N,R,a,U)\bigr)+E\le F,$$
--   then $X_j(\zeta(x+it_c))>0$ for every $|x-\sigma_c|\le r$, where $X_j$ is the
--   defined octant projection. Quotients use Lean's total real division.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Octant.lean#L665-L794

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
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
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
import Theorems.Thm_H1000Oct_checkOct_sound
import Theorems.Thm_H1000Oct_emFinite_taylor_le_G
import Theorems.Thm_H1000Oct_norm_add_nat_le_abs
import Theorems.Thm_H1000Oct_norm_emCorr_le_norm
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace H1000Oct
end H1000Oct
open H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/

































/-! ## D. The piece. -/

theorem H1000Oct.piece_octX_pos (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ) (kk : ℤ)
    (hchk : checkOct c o K N p s1.acc s2.acc rn rd FN FD kk = true)
    (R L a U G E : ℝ) (hrR : (rn : ℝ) / rd ≤ R) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P) (hRL : R * L ≤ 1)
    (ha : 0 < a) (hA : (a + R) ^ 2 ≤ (σc - 1) ^ 2 + tc ^ 2)
    (hU0 : 0 ≤ U) (hU : (|σc| + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2)
    (hG : ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-sOfG σc tc)‖ ≤ G)
    (hE : ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      ‖riemannZeta (sOfG x tc) - emFinite K (sOfG x tc) N‖ ≤ E)
    (hbudget : G * (Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N R a U) + E ≤ (FN : ℝ) / FD) :
    ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      0 < ArgHoriz.octX kk (riemannZeta ((x : ℂ) + (tc : ℂ) * I)) := by sorry
