-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_good_primes
-- name    : ModularCurve.JZero.jensen_good_primes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/b9e73a4d-390b-51f1-bd81-9f9c64ece653
-- title:
--   Non-archimedean Jensen formula at good places, cusp included
-- statement:
--   Let $N\ge 1$ and let $\bar F_N=$ `modularFunctionFieldBar N` be the base change to $\bar{\mathbb Q}$ of the full modular function field of level $N$, viewed inside the Laurent series over $\bar{\mathbb Q}$; write $\bar\infty$ for the place `cuspInftyBar N` and $E$ for `embDivisor N` $=(\mathrm{embDegree}\,N)\cdot\bar\infty$. Let $s:\mathrm{Fin}\,r\to\bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\bar{\mathbb Q}$ and spans the Riemann–Roch space $L(E)=\{f:\ |f|_v\le\exp(E_v)\ \forall v\}$, and let $t$ satisfy $\mathrm{ord}_{\bar\infty}t=1$. Then there is a finite set $S$ of primes such that the following holds for every $k\in\mathbb N$, every nonzero $u\in L(kE)$, every divisor $B$ with $B_w=\mathrm{ord}_w u+kE_w$ at all places $w$, every number field $L\subset\bar{\mathbb Q}$, every finite place $\nu$ of $L$ with $\nu(p)=1$ for all $p\in S$, every family $x$ of vectors $x_w\in L^r$ whose images in $\bar{\mathbb Q}$ are the pivot-normalised evaluation vectors $\mathrm{evalVec}\,s\,w=\big((s_i/s_{i_w})(w)\big)_i$ for all $w$ in the support of $B$ and also for $w=\bar\infty$, and every $c\in L$ whose image is $\mathrm{regVal}=(u\,s_{i_{\bar\infty}}^{-k}t^{-e})(\bar\infty)$ with $e=\max(B_{\bar\infty},0)$: there exists $m\in\mathbb R$ with $$\sum_{w\neq\bar\infty}B_w\,\mathrm{prox}_\nu(x_{\bar\infty},x_w)=k\log\sup_i\nu(x_{\bar\infty,i})-\log\nu(c)-m,$$ the sum being over the support of $B$ with $\bar\infty$ erased, and moreover, with the same $m$, for every place $v$ with $B_v=0$ whose coordinates $x_v$ likewise reduce to $\mathrm{evalVec}\,s\,v$ and every $a\in L$ with image $\mathrm{secVal}=(u\,s_{i_v}^{-k})(v)$, $$\sum_{w}B_w\,\mathrm{prox}_\nu(x_v,x_w)=k\log\sup_i\nu(x_{v,i})-\log\nu(a)-m.$$ Here $\mathrm{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{i,j}\nu(x_iy_j-x_jy_i)$ is the chordal proximity, and evaluation at a place is residue evaluation in its valuation ring.
--
--   This is the non-archimedean Jensen formula (a projective form of Gauss's lemma) for the projective model of the modular curve of level $N$ given by a basis of $L(E)$: at a finite place of good reduction the weighted proximity of a point to the zero divisor of a section $u$ of degree $k$ equals its sup-norm contribution minus the logarithm of the value of $u$ in the pivot trivialisation, up to a constant $m$ independent of the point. It specialises [`ModularCurve.JZero.jensen_good_at`](thm.html#ModularCurve.JZero.jensen_good_at) so that the line at the cusp $\bar\infty$, regularised by a uniformiser $t$, shares the constant $m$ with the lines at places off the support of $B$, and is used in [`ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le`](thm.html#ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_good_primes.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_good_primes (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
          = (k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c) - m ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          (B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
            = (k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m := by sorry
