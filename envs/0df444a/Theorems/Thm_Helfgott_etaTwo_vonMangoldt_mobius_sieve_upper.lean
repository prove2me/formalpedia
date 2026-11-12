-- Prove2me | Theorems.Thm_Helfgott_etaTwo_vonMangoldt_mobius_sieve_upper
-- name    : Helfgott.etaTwo_vonMangoldt_mobius_sieve_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T20:42:46.785605+00:00
-- url     : https://prove2.me/theorems/8fcc3654-acb1-4d5f-bd2d-dbdf4ef1360f
-- title:
--   A complete exponential-sum bound with Mobius cancellation in both Type I terms
-- statement:
--   Let $U,V,R,q,a$ be natural numbers with $2\le R\le V$, $2\le q\le U$, and $(a,q)=1$. Suppose $y\ge8$, $8U\le y$, $4V\le y$, $UV\le y$, $q^2V|\beta|\le1$, and $qUV|\beta|\le1/2$. Write $\alpha=a/q+\beta$, $\delta=\beta y$, $M(0)=1$, and $M(\delta)=\min(1,18/(\pi\delta)^2)$ otherwise. Put
--    $$P=V\log4+2\sqrt V\log V,\qquad K=36+8\pi\log2|\delta|,$$
--    $$T_1=\frac yq\bigl(\log(y/q)M(\delta)+\log4\bigr)+2\lfloor U/q\rfloor\bigl((\log y+\log4)K+16\log2\bigr)
--    +\frac{36\log(y+2)q^2U}{y}\min\{U+1,8(\lfloor U/q\rfloor+1)\},$$
--    $$T_C=\frac yq M(\delta)(\log V+\log4+4+\log q)+2UKP+\frac{72Uq(U+q)}yVP.$$
--    Let $J=\lfloor\log_2\lfloor\lfloor y/(V+1)\rfloor/(U+1)\rfloor\rfloor+1$ and $C_j=(U+1)2^j$, using the natural-number logarithm equal to zero at zero.
--    For a block $[C,D)$ put
--    $$T=\lfloor y/C\rfloor,\quad N=T+1,\quad L=\lfloor\max(D-C,0)/q\rfloor+1,$$
--    $$K_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{\operatorname{lcm}(d,e)},\quad E=DK_U+U^2,\quad H=\log N(N\log4+2\sqrt N\log N),$$
--    $$A_0=16(\log2)^2y/C,\quad B_0'=224\log2\,D/y,$$
--    $$Q(C,D)=HEL\left(2A_0+\min\{2B_0'q^2,A_0+2q\sqrt{A_0B_0'}\}\right),$$
--    $$A_1=16(\log2)^2qL\left(\frac N{\varphi(q)\log R}+R^4\right)(1+2\pi ND|\beta|)^2,$$
--    $$S(C,D)=\sqrt{A_1(N\log N\log4)E}+8\log2\sqrt N\log N\sqrt{\max(D-C,0)}\sqrt E.$$
--    Then
--    $$\left|\sum_{n\ge1}\Lambda(n)\eta_2(n/y)e(\alpha n)\right|
--    \le T_1+T_C+\sum_{j=0}^{J-1}\min\{\sqrt{Q(C_j,C_{j+1})},S(C_j,C_{j+1})\}.$$
--    Here $e(t)=\exp(2\pi it)$ and $\eta_2(t)=4\max(\log2-|\log(2t)|,0)$ for $t>0$, zero otherwise. The Type I and correction bounds preserve resonant Mobius cancellation and include all discretization and nonresonant errors. The estimate is unconditional, with conservative constants and explicit phase-range hypotheses.
-- source:
--   Vaughan identity, quadratic rational kernels, classical finite Selberg sieve and Fourier orthogonality, in the setting of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Retained source proofs carry Apache 2.0 attribution to raresbuhai, marwahaha and Gershon Bialer in the standalone certificate. New smoothing factorization, sieve weights, complete phase perturbation and prime-power assembly formalized by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
open Helfgott Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.etaTwo_vonMangoldt_mobius_sieve_upper (U V R q a : ℕ)
    (hR : 2≤R) (hRV : R≤V) (hq : 2≤q) (hqU : q≤U) (ha : Nat.Coprime a q)
    (y beta : ℝ) (hy : 8≤y) (hUy : 8*(U:ℝ)≤y) (hVy : 4*(V:ℝ)≤y)
    (hUV : (U:ℝ)*(V:ℝ)≤y) (hb : (q:ℝ)^2*(V:ℝ)*|beta|≤1)
    (hp : (q:ℝ)*(U:ℝ)*(V:ℝ)*|beta|≤1/2) :
    let delta := beta*y
    let M := if delta=0 then (1:ℝ) else min 1 (18/(Real.pi*delta)^2)
    let P := (V:ℝ)*Real.log 4+2*Real.sqrt (V:ℝ)*Real.log V
    let K := 36+8*Real.pi*Real.log 2*|delta|
    let T1 := y/(q:ℝ)*(Real.log (y/(q:ℝ))*M+Real.log 4)+
      ((U/q:ℕ):ℝ)*2*((Real.log y+Real.log 4)*K+16*Real.log 2)+
      min ((4*Real.log (y+2))*(9*(q:ℝ)^2*(U:ℝ)*(U+1:ℕ)/y))
        (288*Real.log (y+2)*(U:ℝ)*(q:ℝ)^2*((U/q+1:ℕ):ℝ)/y)
    let TC := (y/(q:ℝ))*M*(Real.log V+Real.log 4+4+Real.log q)+
      (U:ℝ)*2*K*P+(72*(U:ℝ)*(q:ℝ)*((U:ℝ)+q)/y)*((V:ℝ)*P)
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
    ‖expSum (fun n => ((vonMangoldt n*etaTwo ((n:ℝ)/y):ℝ):ℂ))
      (((a:ℝ)/(q:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖ ≤ T1+TC+
      ∑ j ∈ range J, min (Real.sqrt (Q ((U+1)*2^j) ((U+1)*2^(j+1))))
        (S ((U+1)*2^j) ((U+1)*2^(j+1))) := by sorry
