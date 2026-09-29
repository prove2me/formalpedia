-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_arch_at_of_nonCuspidal
-- name    : ModularCurve.JZero.jensen_arch_at_of_nonCuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a5e17dc8-590c-5f6d-a5f2-235fe7b20ba2
-- title:
--   Archimedean Jensen line at ∞̄ and non-cuspidal places
-- statement:
--   Let $N\ge 1$ and let $s:\mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of `embDivisor N` $=$ `embDegree N` times the divisor of multiplicity one at the place `cuspInftyBar N`, the space of $f$ with $v(f)\le \exp(\,$`embDivisor N`$\,v)$ at every place $v$ of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$. Then there is $c_0\in\mathbb R$ with the following property. Let $k\in\mathbb N$, let $u\ne 0$ lie in the Riemann–Roch space of $k\cdot$`embDivisor N`, let $B$ be the divisor with $B(w)=\mathrm{ord}_w(u)+k\,$`embDivisor N`$(w)$ for all $w$, let $L\subset\overline{\mathbb Q}$ be a number field with an infinite place $\nu$, and let $x$ assign to each place $w$ a row $x_w\in L^{r}$ such that for $w\in\operatorname{supp}B$ the image of $x_{w,i}$ in $\overline{\mathbb Q}$ is `evalVec s w i`, the value at $w$ of $s_i$ divided by the pivot coordinate. Then there is $m\in\mathbb R$, independent of the place chosen next, such that for every place $v_0$ that either equals `cuspInftyBar N` or has the element of `modularFunctionFieldBar N` given by the coefficientwise image of `jq` in its valuation subring, every $t$ with $\mathrm{ord}_{v_0}(t)=1$ whenever $B(v_0)>0$, provided the row $x_{v_0}$ also represents `evalVec s v₀`, every $c\in L$ whose image is `regVal s v₀ t k (B v₀).toNat u`, i.e. the value at $v_0$ of $u\,s_{\mathrm{piv}}^{-k}t^{-e}$ with $e=\max(B(v_0),0)$, and every $y\in L^{r\times r}$ such that, when $B(v_0)>0$, the image of $y_{(i,j)}$ is `regVal s v₀ t 1 1` applied to $\,$`evalVec s v₀` $_i\,s_j-$ `evalVec s v₀` $_j\,s_i$ and $\sup_p\nu(y_p)\ne 0$, one has $$\Bigl|\sum_{w\ne v_0}B(w)\,\mathrm{prox}_\nu(x_{v_0},x_w)-\bigl((k-2B(v_0))\log\sup_i\nu(x_{v_0,i})+B(v_0)\log\sup_p\nu(y_p)-\log\nu(c)-m\bigr)\Bigr|\le c_0\,k,$$ where $\mathrm{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{i,j}\nu(x_iy_j-x_jy_i)$ and the sum runs over the support of $B$ with $v_0$ deleted.
--
--   This is the archimedean Jensen inequality for the coordinate embedding of $X_0(N)$ attached to a basis of the Riemann–Roch space of `embDivisor N`, in the form valid at the cusp `cuspInftyBar N` and at every place where the modular invariant is regular: the weighted sum of chordal proximities of the base row $x_{v_0}$ against the rows of the divisor $B=\operatorname{div}(u)+k\,$`embDivisor N` agrees with a regularised local line in $k$, $B(v_0)$, the row sup-norm, the tangent datum $y$ and the regularised value $c$, up to $c_0k$. It is obtained from the point-wise archimedean Jensen line [`ModularCurve.JZero.jensen_arch_embedding`](thm.html#ModularCurve.JZero.jensen_arch_embedding) together with the approximation of $v_0$ by algebraic places provided by [`ModularCurve.JZero.exists_seq_tendsto_place`](thm.html#ModularCurve.JZero.exists_seq_tendsto_place), and is used in [`ModularCurve.JZero.sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le`](thm.html#ModularCurve.JZero.sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_arch_at_of_nonCuspidal.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.jensen_arch_at_of_nonCuspidal (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.InfinitePlace ↥L),
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
        ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        |((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
              + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m)|
          ≤ c₀ * k := by sorry
