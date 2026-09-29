-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_good_at_le
-- name    : ModularCurve.JZero.jensen_good_at_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/806b88c5-5cfa-57ec-b859-151e41389c4f
-- title:
--   Explicit one-sided Jensen inequality at good finite places
-- statement:
--   Fix $N\ge 1$ and a family $s\colon \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` which is an embedding basis, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of the divisor `embDivisor N` $=(\mathrm{embDegree}\,N)\cdot(\bar\infty)$, $\bar\infty$ being the place `cuspInftyBar N`. Then there is a finite set $S$ of primes such that the following holds for: every $k$; every number field $L\subset\overline{\mathbb Q}$; every family $c_\varphi\in L$ indexed by maps $\varphi\colon \mathrm{Fin}\,k\to\mathrm{Fin}\,r$; every nonzero $u$ with $u=\sum_\varphi c_\varphi\prod_{l} s_{\varphi(l)}$; every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+k\,(\mathrm{embDivisor}\,N)(w)$ at all places $w$; every finite place $\nu$ of $L$ with $\nu(p)=1$ for all $p\in S$; every place $v_0$; every divisor $B'$ with $0\le B'(w)\le (B-B(v_0)v_0)(w)$ for all $w$; every $x_w\in L^{r}$ whose image in $\overline{\mathbb Q}$ is the pivot-normalised evaluation vector $\mathrm{evalVec}\,s\,w$, for $w$ in the support of $B'$ and for $w=v_0$; every $t$ with $\mathrm{ord}_{v_0}(t)=1$ when $B(v_0)>0$; every $a\in L$ equal to $\mathrm{regVal}\,s\,v_0\,t\,k\,B(v_0)^{+}\,u$, that is the value at $v_0$ of $u\,s_{\mathrm{piv}}^{-k}t^{-B(v_0)}$; and every $y\in L^{\mathrm{Fin}\,r\times\mathrm{Fin}\,r}$ with, when $B(v_0)>0$, $y_p$ the regularised value $\mathrm{regVal}\,s\,v_0\,t\,1\,1$ of $(\mathrm{evalVec}\,s\,v_0)_{p_1}s_{p_2}-(\mathrm{evalVec}\,s\,v_0)_{p_2}s_{p_1}$ and $\sup_p\nu(y_p)\neq 0$. The conclusion is $$\log \nu(a)\le \log\sup_\varphi \nu(c_\varphi)+(k-2B(v_0))\log\sup_i\nu(x_{v_0,i})+B(v_0)\log\sup_p\nu(y_p)-\sum_w B'(w)\,\mathrm{prox}_\nu(x_{v_0},x_w),$$ where $\mathrm{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{p}\nu(x_{p_1}y_{p_2}-x_{p_2}y_{p_1})$.
--
--   This is the one-sided, fully explicit form of the regularised Jensen inequality at finite places of good reduction: the inexplicit $\nu$-adic content of $u$ is replaced by the supremum of the coefficients $c_\varphi$ of an arbitrary presentation of $u$ over the degree-$k$ monomials in the embedding basis, and only the part $B'$ of the zero divisor away from $v_0$ is retained. It feeds the height estimates on $J_0(N)$ used in [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_good_at_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_good_at_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w)) := by sorry
