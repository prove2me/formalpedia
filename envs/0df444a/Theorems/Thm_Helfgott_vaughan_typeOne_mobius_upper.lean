-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeOne_mobius_upper
-- name    : Helfgott.vaughan_typeOne_mobius_upper
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T20:22:17.510108+00:00
-- url     : https://prove2.me/theorems/a8c325d5-c52f-4b03-a0de-57224fd8c61c
-- title:
--   A Type I bound preserving resonant Mobius cancellation and Fourier decay
-- statement:
--   Let $a\in\mathbb Z$, $2\le q\le U$, $(a,q)=1$, $y\ge8$, $8U\le y$, and $qU|\beta|\le1/2$. Write $\alpha=a/q+\beta$, $\delta=\beta y$, and let $M(0)=1$, $M(\delta)=\min(1,18/(\pi\delta)^2)$ otherwise. Define $T_U(n)=\sum_{d\mid n,\ d\le U}\mu(d)\log(n/d)$ and $\eta_2(t)=4\max(\log2-|\log(2t)|,0)$ for $t>0$, zero otherwise. Then
--    $$\left|\sum_{n\ge1}T_U(n)\eta_2(n/y)e(\alpha n)\right|
--    \le \frac yq\bigl(\log(y/q)M(\delta)+\log4\bigr)
--    +2\lfloor U/q\rfloor\bigl((\log y+\log4)(36+8\pi\log2|\delta|)+16\log2\bigr)
--    +\frac{36\log(y+2)q^2U}{y}\min\bigl(U+1,8(\lfloor U/q\rfloor+1)\bigr).$$
--    The three terms respectively bound the resonant main term, its explicit quadrature error, and the nonresonant contribution. All constants are conservative and the estimate is unconditional.
-- source:
--   Classical Vaughan decomposition and resonant Mobius cancellation, as in Helfgott, Minor arcs for Goldbach, arXiv:1205.5252v4, Section 3. Local constants are proved by elementary coprime Mobius cancellation, Lipschitz quadrature and a limiting discrete second-difference argument for Fourier decay. Retained arithmetic infrastructure carries Apache 2.0 attribution to raresbuhai (submissions 63b25d14-2999-434f-b84f-5af50fbd02fa, 4b19f26e-e6f8-4a14-8cf6-e0ea33b44440, dc167013-7b1b-47a5-bd68-36e63ad77223) and rational grid infrastructure to marwahaha / Gershon Bialer (968ef56d-d4b0-42b8-99aa-5a18c7253fab).

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
open Helfgott Finset
open scoped BigOperators

theorem Helfgott.vaughan_typeOne_mobius_upper (a : ℤ) (q U : ℕ) (hq : 2 ≤ q)
    (hqU : q ≤ U) (haq : Nat.Coprime a.natAbs q) (y beta : ℝ)
    (hy : 8 ≤ y) (hUy : 8*(U:ℝ) ≤ y) (hbeta : (q:ℝ)*|beta| * (U:ℝ) ≤ 1/2) :
    let delta := beta*y
    let M := if delta=0 then (1:ℝ) else min 1 (18/(Real.pi*delta)^2)
    ‖expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n:ℝ)/y):ℝ):ℂ))
      (((a:ℝ)/(q:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖ ≤
      y/(q:ℝ)*(Real.log (y/(q:ℝ))*M+Real.log 4)+
      ((U/q:ℕ):ℝ)*2*((Real.log y+Real.log 4)*(36+8*Real.pi*Real.log 2*|delta|)+16*Real.log 2)+
      min ((4*Real.log (y+2))*(9*(q:ℝ)^2*(U:ℝ)*(U+1:ℕ)/y))
        (288*Real.log (y+2)*(U:ℝ)*(q:ℝ)^2*((U/q+1:ℕ):ℝ)/y) := by sorry
