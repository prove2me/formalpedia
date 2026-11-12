-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeTwo_quadratic_block
-- name    : Helfgott.vaughan_typeTwo_quadratic_block
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T18:36:46.961368+00:00
-- url     : https://prove2.me/theorems/dd939ae9-d868-4aa5-b224-042e767e3250
-- title:
--   Quadratic smoothing correlation bound for actual Vaughan Type II blocks
-- statement:
--   Let $U\ge1$, $C\ge U+1$, $V,D$ be natural cutoffs, $y>0$, $q\ge2$, and $\theta=a/q+\beta$ with $(|a|,q)=1$ and $|\beta|\le q^{-2}$. Set $T=\lfloor y/C\rfloor$, $b_U=(\mu 1_{(U,\infty)})*1$, and
--   $$K_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{\operatorname{lcm}(d,e)},\quad A=16(\log2)^2\frac yC,\quad B=224\log2\frac Dy,$$
--   $$E(T)=\log(T+1)\bigl((T+1)\log4+2\sqrt{T+1}\log(T+1)\bigr).$$
--   For Helfgott's compact smoothing $\eta_2$, the actual Type II block satisfies
--   $$\left|\sum_{d=1}^{T}\sum_{C\le m<D}\Lambda(d)1_{d>V}b_U(m)\eta_2(dm/y)e(dm\theta)\right|^2
--   \le E(T)(DK_U+U^2)\left(\left\lfloor\frac{D-C}{q}\right\rfloor+1\right)
--   \left[2A+\min\{2Bq^2,A+2q\sqrt{AB}\}\right].$$
--   The rational correlation factor has no logarithmic factor in $q$. The arithmetic energies are evaluated; the signed finite form $K_U$ remains explicit. Summing optimized blocks and bounding this form sharply are separate tasks.
-- source:
--   Classical Cauchy-Schwarz, rational spacing and second-difference cancellation for Helfgott compact smoothing; context https://arxiv.org/html/1205.5252v4. Finite correlation, Schur and arithmetic energy proofs retained with attribution from accepted submission dc167013-7b1b-47a5-bd68-36e63ad77223 by raresbuhai (Apache 2.0); grid spacing retained from 968ef56d-d4b0-42b8-99aa-5a18c7253fab by marwahaha with Apache attribution to Gershon Bialer. Product second variation, quadratic correlations, support completion and the new block estimate proved by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
open Helfgott Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.vaughan_typeTwo_quadratic_block (U V C D q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hU : 1 ≤ U) (hC : U+1 ≤ C) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (hy : 0 < y) (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let T := ⌊y/(C:ℝ)⌋₊
    let A := (4*Real.log 2)^2*y/(C:ℝ)
    let B := 224*Real.log 2*(D:ℝ)/y
    ‖∑ d ∈ Icc 1 T, ∑ m ∈ Ico C D,
      ((arithmeticTail V vonMangoldt d:ℝ):ℂ)*
      (((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m:ℝ):ℂ)*
      ((etaTwo (((d*m:ℕ):ℝ)/y):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ)))‖^2 ≤
      (Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)))*
      ((D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
        ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2)*
      (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B))) := by sorry
