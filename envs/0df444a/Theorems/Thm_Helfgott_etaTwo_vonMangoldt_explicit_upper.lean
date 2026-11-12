-- Prove2me | Theorems.Thm_Helfgott_etaTwo_vonMangoldt_explicit_upper
-- name    : Helfgott.etaTwo_vonMangoldt_explicit_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T18:46:27.233777+00:00
-- url     : https://prove2.me/theorems/8734cb98-3bbe-4f9e-a511-e4dd98ae892e
-- title:
--   A complete explicit Vaughan bound for the actual etaTwo prime exponential sum
-- statement:
--   Let $U\ge1,V$ be natural cutoffs, $y\ge8$, $8U\le y$, $4V\le y$, $q\ge2$, and $\theta=a/q+\beta$ with $(|a|,q)=1$ and $|\beta|\le q^{-2}$. Define
--   $$F(Z)=\frac{9q^4}{y}+\frac{24y}{q}(1+\log(Z+q))+30(Z+q),\qquad B_0=\min(UV,\lfloor y\rfloor),$$
--   $$M=\left\lfloor\frac y{V+1}\right\rfloor,\quad J=\left\lfloor\log_2\left\lfloor\frac M{U+1}\right\rfloor\right\rfloor+1,\quad C_j=(U+1)2^j,$$
--   where the natural-number logarithm is defined to be zero at zero. For $C,D\ge1$ put
--   $$T_C=\lfloor y/C\rfloor,\quad A_C=16(\log2)^2y/C,\quad B_D=224\log2\,D/y,$$
--   $$K_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{\operatorname{lcm}(d,e)},\qquad E(T)=\log(T+1)((T+1)\log4+2\sqrt{T+1}\log(T+1)),$$
--   $$R(C,D)=E(T_C)(DK_U+U^2)\left(\left\lfloor\frac{D-C}{q}\right\rfloor+1\right)
--   \left[2A_C+\min\{2B_Dq^2,A_C+2q\sqrt{A_CB_D}\}\right].$$
--   Then the actual smoothed prime sum satisfies
--   $$\left|\sum_{n\ge1}\Lambda(n)\eta_2(n/y)e(n\theta)\right|\le4\log(y+2)F(U)+\log(B_0+q)F(B_0)+\sum_{j=0}^{J-1}\sqrt{R(C_j,C_{j+1})}.$$
--   All terms are explicit finite arithmetic or elementary expressions. The bound combines all terms of Vaughan's identity with exact support and dyadic decomposition. It is a conservative estimate, not the final optimized numerical Goldbach minor-arc estimate.
-- source:
--   Vaughan identity, second-difference cancellation, rational spacing and finite Schur estimates, in the setting of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Arithmetic, finite correlation and energy proofs retain attribution to raresbuhai submissions 63b25d14-2999-434f-b84f-5af50fbd02fa and dc167013-7b1b-47a5-bd68-36e63ad77223 (Apache 2.0). Rational spacing retains attribution to marwahaha submission 968ef56d-d4b0-42b8-99aa-5a18c7253fab and Gershon Bialer. Quadratic smoothing, complete outer bounds, support partition and combined bound proved by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
open Helfgott Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.etaTwo_vonMangoldt_explicit_upper (U V q : ℕ) (a : ℤ)
    (hU : 1 ≤ U) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (y theta beta : ℝ) (hy : 8 ≤ y) (hUy : 8*(U:ℝ) ≤ y) (hVy : 4*(V:ℝ) ≤ y)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let B := min (U*V) ⌊y⌋₊
    let J := Nat.log 2 (⌊y/(V+1:ℕ)⌋₊/(U+1))+1
    let R : ℕ → ℕ → ℝ := fun C D =>
    let T := ⌊y/(C:ℝ)⌋₊
      let A := (4*Real.log 2)^2*y/(C:ℝ)
      let B := 224*Real.log 2*(D:ℝ)/y
      (Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)))*
        ((D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
          ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2)*
        (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B)))
    ‖expSum (fun n => ((vonMangoldt n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log (y+2))*(9*(q:ℝ)^4/y+24*y/(q:ℝ)*(1+Real.log (U+q:ℕ))+30*(U+q:ℕ))+
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ))+
      ∑ j ∈ range J, Real.sqrt (R ((U+1)*2^j) ((U+1)*2^(j+1))) := by sorry
