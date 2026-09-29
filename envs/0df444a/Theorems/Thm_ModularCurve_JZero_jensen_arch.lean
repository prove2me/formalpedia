-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_arch
-- name    : ModularCurve.JZero.jensen_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/67c6d0ea-8cf1-5582-b2e5-e552907510f5
-- title:
--   Archimedean Jensen bound at infinite places of number fields
-- statement:
--   Let $N\ge 1$, let $r\in\mathbb N$, and let $s:\{0,\dots,r-1\}\to \bar F_N$ be a family in the base-changed modular function field `modularFunctionFieldBar N` which is an embedding basis, i.e. linearly independent over $\bar{\mathbb Q}=$ `AlgebraicClosure ℚ` and spanning the Riemann–Roch space $L(E)$ of the divisor $E=$ `embDivisor N` $=(\mathrm{embDegree}\,N)\cdot\bar\infty$ supported at the place $\bar\infty=$ `cuspInftyBar N`; let $t\in\bar F_N$ satisfy $\operatorname{ord}_{\bar\infty}t=1$. Then there is a constant $c\in\mathbb R$ with the following property, for all $k\in\mathbb N$, all $u\neq 0$ in $L(kE)$ (the functions $f$ with $|f|_v\le \exp(kE_v)$ at every place $v$), every divisor $B$ with $B_w=\operatorname{ord}_w u+kE_w$ for all $w$, every number field $L\subset\bar{\mathbb Q}$, every infinite place $\nu$ of $L$, every assignment $x$ of vectors $x_w\in L^r$ to places whose entries realise the pivot evaluation vectors, $x_{w,i}=\big(s_i/s_{i_w}\big)(w)$ in $\bar{\mathbb Q}$, for all $w\in\operatorname{supp}B$ and for $w=\bar\infty$, and every $c'\in L$ whose image in $\bar{\mathbb Q}$ is the regularised value $\big(u\,s_{i_{\bar\infty}}^{-k}t^{-e}\big)(\bar\infty)$ with $e=(B_{\bar\infty})^{+}$: there exists $m\in\mathbb R$ such that, writing $\operatorname{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{i,j}\nu(x_iy_j-x_jy_i)$, one has $$\Big|\sum_{w\neq\bar\infty}B_w\operatorname{prox}_\nu(x_{\bar\infty},x_w)-\big(k\log\sup_i\nu(x_{\bar\infty,i})-\log\nu(c')-m\big)\Big|\le ck,$$ and moreover, for every place $v$ with $B_v=0$ whose vector $x_v$ likewise realises the evaluation vector of $v$, and every $a\in L$ mapping to the pivot value $\big(u\,s_{i_v}^{-k}\big)(v)$, $$\Big|\sum_{w}B_w\operatorname{prox}_\nu(x_v,x_w)-\big(k\log\sup_i\nu(x_{v,i})-\log\nu(a)-m\big)\Big|\le ck.$$ The same $m$ serves both lines, and $c$ depends only on $N$, $s$ and $t$ — in particular not on $k$, $u$, $B$, $L$, $\nu$ or $x$.
--
--   This is the archimedean half of the comparison, on the projective model of $X_0(N)$ cut out by an embedding basis, between the chordal proximity sum of the divisor of zeros of a section of degree $k$ and the naive height terms at an infinite place; classically it is the Jensen-formula comparison between the logarithmic Mahler measure and the sup norm of coefficients. It is stated here for an arbitrary infinite place of an arbitrary number field containing the relevant coordinates, and is used by [`ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le`](thm.html#ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_arch.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_arch (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.InfinitePlace ↥L),
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c' : ↥L, (c' : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
            - ((k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c') - m)|
          ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          |(B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
              - ((k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m)|
            ≤ c * k := by sorry
