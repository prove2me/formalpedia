-- Prove2me | Theorems.Thm_ModularCurve_JZero_jensen_bad_at_le
-- name    : ModularCurve.JZero.jensen_bad_at_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a6fdfe72-b882-54d3-bf37-28346c278663
-- title:
--   One-sided Jensen inequality at bad finite places
-- statement:
--   Fix $N \ge 1$ and a family $s : \mathrm{Fin}\,r \to \overline{\mathcal F}_N$ in the modular function field of level $N$ base-changed to $\overline{\mathbb Q}$, assumed to be an `IsEmbBasis`: linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space $\{f : \forall w,\ w(f) \le \exp(E(w))\}$ of the divisor $E = \mathrm{embDivisor}\,N = \mathrm{embDegree}(N)\cdot[\,\mathrm{cuspInftyBar}\,N\,]$. Let $S_0$ be a finite set of naturals. The assertion is that there exists $c_0 \in \mathbb R$, depending only on these data, such that the following holds for every $k$, every number field $L \subseteq \overline{\mathbb Q}$, every family $c$ of elements of $L$ indexed by maps $\mathrm{Fin}\,k \to \mathrm{Fin}\,r$, and every nonzero $u$ with $u = \sum_\varphi c_\varphi \prod_l s_{\varphi(l)}$: whenever $B$ is the divisor with $B(w) = \mathrm{ord}_w(u) + k\,E(w)$ at every place $w$, $\nu$ is a finite place of $L$, $p \in S_0$ is prime with $\nu(p) < 1$, $v_0$ is a place, $B'$ is a divisor with $0 \le B'(w) \le (B - B(v_0)v_0)(w)$ for all $w$, $x$ assigns to each place $w$ a row in $L^r$ whose image in $\overline{\mathbb Q}$ is $\mathrm{evalVec}\,s\,w$, that is $w\text{-}\mathrm{evalAt}(s_i \cdot s_{\mathrm{pivotIndex}}^{-1})$, for $w \in \mathrm{supp}\,B'$ and for $w = v_0$, $t$ satisfies $\mathrm{ord}_{v_0}(t) = 1$ provided $B(v_0) > 0$, $a \in L$ has image the regularised value $\mathrm{evalAt}_{v_0}\!\big(u \cdot s_{\mathrm{pivotIndex}}^{-k} \cdot t^{-(B(v_0))_+}\big)$, and $y : \mathrm{Fin}\,r \times \mathrm{Fin}\,r \to L$ satisfies, provided $B(v_0) > 0$, that $y_{(i,j)}$ has image $\mathrm{evalAt}_{v_0}\!\big((\mathrm{evalVec}\,s\,v_0)_i\, s_j - (\mathrm{evalVec}\,s\,v_0)_j\, s_i \cdot s_{\mathrm{pivotIndex}}^{-1} t^{-1}\big)$ and $\sup_{(i,j)} \nu(y_{(i,j)}) \ne 0$, then $$\log \nu(a) \le \log \sup_\varphi \nu(c_\varphi) + (k - 2B(v_0))\log \sup_i \nu(x_{v_0,i}) + B(v_0)\log \sup_{(i,j)} \nu(y_{(i,j)}) - \sum_{w \in \mathrm{supp}\,B'} B'(w)\,\mathrm{prox}_\nu(x_{v_0}, x_w) + c_0\,k\,\big({-\log \nu(p)}\big),$$ where $\mathrm{prox}_\nu(x,y) = \log\sup_i \nu(x_i) + \log\sup_i \nu(y_i) - \log\sup_{(i,j)} \nu(x_i y_j - x_j y_i)$.
--
--   This is the bad-place edition of the one-sided local Jensen estimate for sections of the embedding line bundle on the modular curve of level $N$: the same upper bound as at good places, with an extra defect linear in the monomial degree $k$ and normalised by $\log(1/\nu(p))$, so that summing over the places above the primes of $S_0$ contributes at most $c_0 k \sum_{p \in S_0} \log p$. It feeds the height-form estimates on the degree-zero divisor class group, being cited by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_jensen_bad_at_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.jensen_bad_at_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (S₀ : Finset ℕ) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
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
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k * (-Real.log (ν (p : ↥L))) := by sorry
