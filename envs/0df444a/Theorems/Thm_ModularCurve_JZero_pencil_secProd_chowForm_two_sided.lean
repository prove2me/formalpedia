-- Prove2me | Theorems.Thm_ModularCurve_JZero_pencil_secProd_chowForm_two_sided
-- name    : ModularCurve.JZero.pencil_secProd_chowForm_two_sided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9d0b5090-e0ab-57be-bcf4-ba17766da58a
-- title:
--   Two-sided pencil bound for the Chow-side comparison
-- statement:
--   Fix $N\ge 1$ and a family $s=(s_i)_{i<r}$ in $\bar F_N$, the function field of $X_0(N)$ base changed to $\overline{\mathbb Q}$, which is an embedding basis in the sense of `IsEmbBasis`: $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of $E=\mathrm{embDivisor}\,N=d\cdot\bar\infty$ with $d=\mathrm{embDegree}\,N=2g+1$. The assertion is that there is a real constant $c_1$ with the following property, for every ring homomorphism $\sigma:\overline{\mathbb Q}\to\mathbb C$, every $k\in\mathbb N$, every $u\neq 0$ in the Riemann–Roch space of $kE$ and every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+kE(w)$ for all places $w$, under the hypothesis that `ChowReciprocity s (embDivisor N) k' u' B'` holds for all $k'$, all nonzero $u'$ in the Riemann–Roch space of $k'E$ and all divisors $B'$ with $B'(w)=\mathrm{ord}_w(u')+k'E(w)$. Namely, for every covector $c$ and divisor $Z_c$ with $\mathrm{linSec}\,s\,c=\sum_i c_i s_i\neq 0$, $Z_c(w)=\mathrm{ord}_w(\mathrm{linSec}\,s\,c)+E(w)$, and $B(w)=0$ or $Z_c(w)=0$ for every $w$, there exists $M\in\mathbb R$ such that at every place $v$ with $B(v)=Z_c(v)=0$ both of the following hold, where admissibility of a pair $(a,Z_a)$ means $\mathrm{linSec}\,s\,a\neq0$, $Z_a(w)=\mathrm{ord}_w(\mathrm{linSec}\,s\,a)+E(w)$, $\sum_i (\mathrm{evalVec}\,s\,v)_i\,a_i=0$, $Z_a(w)=0$ or $Z_c(w)=0$ for all $w$, and $Z_a(w)=0$ or $B(w)=0$ for all $w\neq v$. Writing
--   $$Q(a,Z_a)=\log\bigl\|\sigma\,\mathrm{secProd}\,s\,k\,u\,(Z_a-\delta_v)\bigr\|+k\Bigl(\log\|\sigma(\mathrm{chowForm}\,s\,Z_c)(a)\|-d\log\sup_i\|\sigma(a_i)\|\Bigr)-k\log\|\sigma(\mathrm{chowForm}\,s\,Z_a)(c)\|,$$
--   with $\mathrm{secProd}\,s\,k\,u\,Z=\prod_w \mathrm{secVal}(s,w,k,u)^{(Z(w))^+}$, $\mathrm{secVal}(s,w,k,u)=w\text{-value of }u\cdot s_{\mathrm{pivot}(w)}^{-k}$, $\mathrm{chowForm}\,s\,Z=\prod_w(\sum_i (\mathrm{evalVec}\,s\,w)_i X_i)^{(Z(w))^+}$ and $(\mathrm{evalVec}\,s\,w)_i$ the $w$-value of $s_i s_{\mathrm{pivot}(w)}^{-1}$: first, $Q(a,Z_a)\le M-k\log\sup_i\|\sigma((\mathrm{evalVec}\,s\,v)_i)\|+c_1k$ for every admissible $(a,Z_a)$; second, some admissible $(a,Z_a)$ satisfies $Q(a,Z_a)\ge M-k\log\sup_i\|\sigma((\mathrm{evalVec}\,s\,v)_i)\|-c_1k$.
--
--   This is the pencil form of the archimedean Chow-side comparison on $X_0(N)$: after the reciprocity identity between Chow forms and section products, the normalised quantity attached to hyperplanes through the coordinate vector of $v$ has a common upper bound $M+c_1k$ and is attained within $c_1k$ of it, uniformly in $v$ off the supports of $B$ and $Z_c$. It is used by [`ModularCurve.JZero.chowSide_arch_embedding_off_support`](thm.html#ModularCurve.JZero.chowSide_arch_embedding_off_support), where the resulting $M$ is identified with the Chow-side local term in the archimedean height estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_pencil_secProd_chowForm_two_sided.lean

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

theorem ModularCurve.JZero.pencil_secProd_chowForm_two_sided (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₁ : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      (∀ (k' : ℕ) (u' : modularFunctionFieldBar N)
          (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          u' ≠ 0 → u' ∈ riemannRochSpace ((k' : ℤ) • embDivisor N) →
          (∀ w, B' w = w.ord u' + ((k' : ℤ) • embDivisor N) w) →
          ChowReciprocity s (embDivisor N) k' u' B') →
      ∀ (c : Fin r → AlgebraicClosure ℚ) (Zc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s c ≠ 0 → (∀ w, Zc w = w.ord (linSec s c) + embDivisor N w) → (∀ w, B w = 0 ∨ Zc w = 0) →
      ∃ M : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 → Zc v = 0 →
        (∀ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
            linSec s a ≠ 0 → (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) →
            (∑ i, evalVec s v i * a i = 0) → (∀ w, Za w = 0 ∨ Zc w = 0) →
            (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) →
            Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
              + k * (Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
                  - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
              - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖
            ≤ M - k * Real.log (⨆ i, ‖σ (evalVec s v i)‖) + c₁ * k) ∧
        (∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
            linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
            (∑ i, evalVec s v i * a i = 0) ∧ (∀ w, Za w = 0 ∨ Zc w = 0) ∧
            (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
            M - k * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - c₁ * k ≤
            Real.log ‖σ (secProd s k u (Za - Finsupp.single v (1 : ℤ)))‖
              + k * (Real.log ‖σ (MvPolynomial.eval a (chowForm s Zc))‖
                  - embDegree N * Real.log (⨆ i, ‖σ (a i)‖))
              - k * Real.log ‖σ (MvPolynomial.eval c (chowForm s Za))‖) := by sorry
