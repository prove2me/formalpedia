-- Prove2me | Theorems.Thm_Helfgott_etaTwo_vonMangoldt_sieve_upper
-- name    : Helfgott.etaTwo_vonMangoldt_sieve_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T19:43:57.648083+00:00
-- url     : https://prove2.me/theorems/3e6caa12-36b0-4e52-b02c-cfa823488e07
-- title:
--   A complete explicit prime exponential-sum bound combining quadratic and prime-sieve Type II estimates
-- statement:
--   Let $U,V,R,q,a$ be natural numbers with $U\ge1$, $2\le R\le V$, $q\ge2$, and $(a,q)=1$. Suppose $y\ge8$, $8U\le y$, $4V\le y$, and $\theta=a/q+\beta$ with $|\beta|\le q^{-2}$. Define
--    $$F(Z)=9q^4/y+(24y/q)(1+\log(Z+q))+30(Z+q),\quad B_0=\min(UV,\lfloor y\rfloor),$$
--    $$J=\left\lfloor\log_2\left\lfloor\frac{\lfloor y/(V+1)\rfloor}{U+1}\right\rfloor\right\rfloor+1,\quad C_j=(U+1)2^j,$$
--    where the natural-number logarithm is zero at zero. For a block $[C,D)$ put
--    $$T=\lfloor y/C\rfloor,\quad N=T+1,\quad L=\lfloor\max(D-C,0)/q\rfloor+1,$$
--    $$K_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{\operatorname{lcm}(d,e)},\quad E=DK_U+U^2,\quad H=\log N(N\log4+2\sqrt N\log N),$$
--    $$A_0=16(\log2)^2y/C,\quad B_0'=224\log2\,D/y,$$
--    $$Q(C,D)=HEL\left(2A_0+\min\{2B_0'q^2,A_0+2q\sqrt{A_0B_0'}\}\right),$$
--    $$A_1=16(\log2)^2qL\left(\frac N{\varphi(q)\log R}+R^4\right)(1+2\pi ND|\beta|)^2,$$
--    $$S(C,D)=\sqrt{A_1(N\log N\log4)E}+8\log2\sqrt N\log N\sqrt{\max(D-C,0)}\sqrt E.$$
--    Then the complete smoothed von Mangoldt sum satisfies
--    $$\left|\sum_{n\ge1}\Lambda(n)\eta_2(n/y)e(n\theta)\right|
--    \le4\log(y+2)F(U)+\log(B_0+q)F(B_0)+\sum_{j=0}^{J-1}\min\{\sqrt{Q(C_j,C_{j+1})},S(C_j,C_{j+1})\}.$$
--    Here $\eta_2(t)=4\max(\log2-|\log(2t)|,0)$ for $t>0$ and zero otherwise. All prime-sieve errors, phase perturbations and higher prime powers are included explicitly; the parameters remain available for further optimization.
-- source:
--   Vaughan identity, quadratic rational kernels, classical finite Selberg sieve and Fourier orthogonality, in the setting of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Retained source proofs carry Apache 2.0 attribution to raresbuhai, marwahaha and Gershon Bialer in the standalone certificate. New smoothing factorization, sieve weights, complete phase perturbation and prime-power assembly formalized by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
open Helfgott Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.etaTwo_vonMangoldt_sieve_upper (U V R q a : ℕ)
    (hU : 1≤U) (hR : 2≤R) (hRV : R≤V) (hq : 2≤q) (ha : Nat.Coprime a q)
    (y theta beta : ℝ) (hy : 8≤y) (hUy : 8*(U:ℝ)≤y) (hVy : 4*(V:ℝ)≤y)
    (htheta : theta=(a:ℝ)/(q:ℝ)+beta) (hbeta : |beta|≤1/(q:ℝ)^2) :
    let B := min (U*V) ⌊y⌋₊
    let J := Nat.log 2 (⌊y/(V+1:ℕ)⌋₊/(U+1))+1
    let Q : ℕ → ℕ → ℝ := fun C D =>
    let T := ⌊y/(C:ℝ)⌋₊
      let A := (4*Real.log 2)^2*y/(C:ℝ)
      let B := 224*Real.log 2*(D:ℝ)/y
      (Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)))*
        ((D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
          ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2)*
        (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B)))
    let S : ℕ → ℕ → ℝ := fun C D =>
    let N := ⌊y/(C:ℝ)⌋₊+1
      let E := (D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
        ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2
      let A := 16*(Real.log 2)^2*(q:ℝ)*(((D-C)/q+1:ℕ):ℝ)*
        ((N:ℝ)/((Nat.totient q:ℝ)*Real.log (R:ℝ))+(R:ℝ)^4)*
          (1+2*Real.pi*(N:ℝ)*(D:ℝ)*|beta|)^2
      Real.sqrt (A*(Real.log (N:ℝ)*Real.log 4*(N:ℝ))*E)+
        8*Real.log 2*Real.sqrt (N:ℝ)*Real.log (N:ℝ)*Real.sqrt ((D-C:ℕ):ℝ)*Real.sqrt E
    ‖expSum (fun n => ((vonMangoldt n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log (y+2))*(9*(q:ℝ)^4/y+24*y/(q:ℝ)*(1+Real.log (U+q:ℕ))+30*(U+q:ℕ))+
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ))+
      ∑ j ∈ range J, min (Real.sqrt (Q ((U+1)*2^j) ((U+1)*2^(j+1))))
        (S ((U+1)*2^j) ((U+1)*2^(j+1))) := by sorry
