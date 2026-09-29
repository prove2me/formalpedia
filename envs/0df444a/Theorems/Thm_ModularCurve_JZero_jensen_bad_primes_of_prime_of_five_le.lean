-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le
-- name    : ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/5d561d9f-5401-5794-ace4-c719092afee1
-- title:
--   Jensen bound at bad primes, prime level at least five
-- statement:
--   Let $N$ be a prime with $N\ge 5$, and work in $\bar F_N=$ `modularFunctionFieldBar N`, the base change to $\bar{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series, with its place $\bar\infty=$ `cuspInftyBar N` and embedding divisor $E=$ `embDivisor N` $=$ `embDegree N` $\cdot\,\bar\infty$. Let $s=(s_i)_{i<r}$ be an embedding basis, i.e. $s$ is linearly independent over $\bar{\mathbb Q}$ and spans the Riemann–Roch space $L(E)$, let $t\in\bar F_N$ satisfy $\operatorname{ord}_{\bar\infty}t=1$, and let $S_0$ be a finite set of primes. Then there is a constant $c\in\mathbb R$, depending only on these data, with the following property. Let $k\in\mathbb N$ and let $u\neq 0$ lie in the Riemann–Roch space of $k\cdot E$; let $B$ be a divisor with $B_w=\operatorname{ord}_w u+k\,E_w$ for every place $w$. Let $L\subset\bar{\mathbb Q}$ be a number field, $\nu$ a finite place of $L$, and $p\in S_0$ with $\nu(p)<1$. Let $x$ assign to each place $w$ a vector $x_w\in L^{r}$ such that, for $w$ in the support of $B$ and also for $w=\bar\infty$, the image of $x_{w,i}$ in $\bar{\mathbb Q}$ is `evalVec s w i`, i.e. the value at $w$ of $s_i/s_{i_w}$ for the pivot index $i_w$ of $w$ (zero when $r=0$). Let $c'\in L$ have image the regularised value `regVal s (cuspInftyBar N) t k (B ∞).toNat u`, namely the value at $\bar\infty$ of $u\,s_{i_{\bar\infty}}^{-k}t^{-e}$ with $e=\max(B_{\bar\infty},0)$. Then there exists $m\in\mathbb R$ such that $$\Bigl|\sum_{w\neq\bar\infty}B_w\,\lambda_\nu(x_{\bar\infty},x_w)-\bigl(k\log\sup_i\nu(x_{\bar\infty,i})-\log\nu(c')-m\bigr)\Bigr|\le c\,k\,(-\log\nu(p)),$$ where $\lambda_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{i,j}\nu(x_iy_j-x_jy_i)$ is the chordal proximity, the sum being over the support of $B$ with $\bar\infty$ erased; and moreover, for the same $m$, for every place $v$ with $B_v=0$ whose coordinate vector $x_v$ again has image `evalVec s v`, and every $a\in L$ whose image is `secVal s v k u`, the value at $v$ of $u\,s_{i_v}^{-k}$, one has $$\Bigl|\sum_{w}B_w\,\lambda_\nu(x_v,x_w)-\bigl(k\log\sup_i\nu(x_{v,i})-\log\nu(a)-m\bigr)\Bigr|\le c\,k\,(-\log\nu(p)).$$
--
--   This is the non-archimedean Jensen (Gauss-lemma) estimate at the finitely many exceptional primes of $S_0$: the two sides of the local counting identity for a section $u$ of a multiple of the embedding divisor differ by at most a constant multiple of $k\,(-\log\nu(p))$, with a single auxiliary constant $m$ serving both the cusp $\bar\infty$ and any place off the support of $B$, and with $c$ independent of the number field $L$ and of the place $\nu$. It is obtained from the corresponding pointwise bound [`ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le) together with the principal-divisor and degree-one facts for $\bar F_N$, and feeds [`ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le`](thm.html#ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le) in the height machinery on $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le (N : ℕ) [NeZero N]
    (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) (S₀ : Finset ℕ)
    (hS₀ : ∀ p ∈ S₀, p.Prime) :
    ∃ c : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L) (p : ℕ), p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c' : ↥L, (c' : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
            - ((k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c') - m)|
          ≤ c * k * (-Real.log (ν (p : ↥L))) ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          |(B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
              - ((k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m)|
            ≤ c * k * (-Real.log (ν (p : ↥L))) := by sorry
