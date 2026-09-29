-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal
-- name    : ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a029f955-d356-5f8c-9e98-2f16a8bafb18
-- title:
--   One-sided archimedean Jensen bound at non-cuspidal base places
-- statement:
--   Fix $N\ge 1$ and a family $s\colon \mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}$-Laurent series, of the full modular function field of level $N$) which is an embedding basis: $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of `embDivisor N` $=\;$`embDegree N`$\cdot\bar\infty$. Then there is a real constant $c_0$ (depending only on $N$ and $s$) such that the following holds for every $k\in\mathbb N$, every number field $L$ realised as an intermediate field of $\overline{\mathbb Q}/\mathbb Q$, every family of coefficients $c\colon (\mathrm{Fin}\,k\to\mathrm{Fin}\,r)\to L$, and every nonzero $u$ in the function field which is the degree-$k$ monomial expansion $u=\sum_{\varphi} c_\varphi\prod_{l} s(\varphi\,l)$: for every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+k\,(\mathrm{embDivisor}\ N)(w)$ at all places $w$, every infinite place $\nu$ of $L$, every place $v_0$ of the function field over $\overline{\mathbb Q}$ which is either the cusp `cuspInftyBar N` or is such that the element coming from the $q$-expansion `jq` lies in the valuation subring of $v_0$ (i.e. $j$ is $v_0$-integral), every divisor $B'$ with $0\le B'\le B-B(v_0)v_0$ pointwise, every $x$ assigning to a place $w$ the normalised coordinate vector $x_{w,i}=$ `evalVec s w i` $=$ the value at $w$ of $s_i/s_{\mathrm{pivot}}$, required for $w$ in the support of $B'$ and for $w=v_0$, every $t$ which is a uniformiser at $v_0$ ($\mathrm{ord}_{v_0}t=1$) whenever $B(v_0)>0$, every $a\in L$ equal to the regularised leading value `regVal s v₀ t k (B v₀).toNat u`, namely the value at $v_0$ of $u\,s_{\mathrm{pivot}}^{-k}t^{-B(v_0)}$, and every $y\colon \mathrm{Fin}\,r\times\mathrm{Fin}\,r\to L$ such that, when $B(v_0)>0$, $y_p$ is the regularised value `regVal s v₀ t 1 1` of $x_{v_0,p_1}s_{p_2}-x_{v_0,p_2}s_{p_1}$ and $\sup_p\nu(y_p)\neq 0$: one has
--   $$\log\nu(a)\le\log\sup_\varphi\nu(c_\varphi)+\bigl(k-2B(v_0)\bigr)\log\sup_i\nu(x_{v_0,i})+B(v_0)\log\sup_p\nu(y_p)-\sum_{w}B'(w)\,\mathrm{prox}_\nu(x_{v_0},x_w)+c_0k,$$
--   where $\mathrm{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{p}\nu(x_{p_1}y_{p_2}-x_{p_2}y_{p_1})$ is the chordal proximity and the sum runs over the support of $B'$.
--
--   This is the archimedean local Jensen-type inequality of the height machinery attached to $J_0(N)$, formulated as a one-sided bound for the logarithmic size of the regularised leading coefficient of a monomial expression in an embedding basis, with a proximity defect term at the auxiliary places and an error linear in the degree $k$; it is the edition restricted to base places $v_0$ that are either the cusp $\bar\infty$ or places of integrality of $j$. It feeds the assembly of the height form, being used by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.InfinitePlace ↥L)
        (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
      ∀ (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
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
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k := by sorry
