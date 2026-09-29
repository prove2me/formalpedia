-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge
-- name    : ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/c267ca1c-8650-5cfd-8c98-32a5be86e601
-- title:
--   Good hyperplane sections through a given place on X₀(N)
-- statement:
--   Fix $N\ge 1$ and a family $s\colon \mathrm{Fin}\,r\to \overline F_N$, where $\overline F_N$ is the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, and assume `IsEmbBasis N s`: $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $L(E)$ of the divisor $E=\mathrm{embDivisor}\,N=(2g+1)\,[\bar\infty]$, where $g$ is the genus of $\overline F_N$ over $\overline{\mathbb Q}$, $\bar\infty$ the distinguished cusp, and $L(D)=\{f:\ \mathrm{ord}_w f\ge -D(w)\ \forall w\}$. Then there is a real constant $c_0$ with the following property. Let $\sigma\colon\overline{\mathbb Q}\to\mathbb C$ be a ring homomorphism, $k\in\mathbb N$, and $u\ne 0$ an element of $L(kE)$; let $B$ be the divisor with $B(w)=\mathrm{ord}_w u+kE(w)$ for all $w$, let $T$ be a finite set of places and $v,y_0$ places with $B(v)=B(y_0)=0$. Then there exist $a\colon \mathrm{Fin}\,r\to\overline{\mathbb Q}$ and a divisor $Z_a$ such that $\mathrm{linSec}\,s\,a=\sum_i a_i s_i\ne 0$, $Z_a(w)=\mathrm{ord}_w(\mathrm{linSec}\,s\,a)+E(w)$ for all $w$, $\sum_i (\mathrm{evalVec}\,s\,v)_i\,a_i=0$, $Z_a(v)=1$, $Z_a(w)=0$ for every $w\in T$ with $w\ne v$, and for every $w\ne v$ either $Z_a(w)=0$ or $B(w)=0$; moreover, writing $\varphi(y)=\log\|\sigma(\mathrm{secVal}\,s\,y\,k\,u)\|-k\log\big(\sup_i\|\sigma((\mathrm{evalVec}\,s\,y)_i)\|\big)$, where $\mathrm{secVal}\,s\,y\,k\,u=y\text{-value of }u\cdot s(\mathrm{pivotIndex}\,s\,y)^{-k}$ and $(\mathrm{evalVec}\,s\,y)_i$ is the $y$-value of $s_i\,s(\mathrm{pivotIndex}\,s\,y)^{-1}$ (both $0$ if $r=0$), one has
--   $$(\mathrm{embDegree}\,N-1)\,\varphi(y_0)-c_0k\ \le\ \sum_y\big(Z_a-[v]\big)(y)\,\varphi(y),$$
--   the sum being the finitely supported sum of $Z_a-\mathrm{Finsupp.single}\,v\,1$ against $\varphi$ and $\mathrm{embDegree}\,N=2g+1$.
--
--   This is the archimedean existence statement for a hyperplane section of the $L(E)$-embedding of $X_0(N)$ that passes simply through a prescribed point $x_v$, avoids a prescribed finite set of places together with the support of the zero divisor of $u$, and whose remaining $2g$ intersection points see the section $u$ almost as well as the reference place $y_0$, with a loss linear in $k$ and otherwise uniform. It is used in [`ModularCurve.JZero.pencil_secProd_chowForm_two_sided`](thm.html#ModularCurve.JZero.pencil_secProd_chowForm_two_sided), in the comparison of section values with Chow-form data on $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
        (v y₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), B v = 0 → B y₀ = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        ((embDegree N : ℝ) - 1) * (Real.log ‖σ (secVal s y₀ k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y₀ i)‖)) - c₀ * k
          ≤ (Za - Finsupp.single v (1 : ℤ)).sum
              (fun y n => (n : ℝ) * (Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))) := by sorry
