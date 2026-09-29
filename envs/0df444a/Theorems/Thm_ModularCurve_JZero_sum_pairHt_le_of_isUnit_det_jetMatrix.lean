-- Prove2me | Theorems.Thm_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix
-- name    : ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/cd5c1e58-219d-54a0-8cf6-cc9405f5120e
-- title:
--   Confluent many-point Jensen inequality for a section frame
-- statement:
--   Fix $N\ge 1$ and a family $s=(s_i)_{i<r}$ in the function field $\overline{F}_N$ of $X_0(N)$ over $\overline{\mathbb Q}$ which is an embedding basis, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of $E=(2g+1)\cdot\bar\infty$, where $g$ is the genus and $\bar\infty$ the place `cuspInftyBar N`; fix naturals $k,m,m'$ and a real $H$. Three hypotheses `hJgood`, `hJbad`, `hJarch` are assumed, all of one shape and summarised here: for every $k$, every number field $L\subseteq\overline{\mathbb Q}$, every coefficient family $c$ indexed by the maps $\mathrm{Fin}\,k\to\mathrm{Fin}\,r$, every non-zero $u=\sum_\varphi c_\varphi\prod_l s_{\varphi(l)}$, every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+k\,E(w)$ for all $w$, every place $\nu$ of $L$, every base place $v_0$ of $\overline F_N$, every divisor $B'$ with $0\le B'\le B-B(v_0)v_0$, every family $x$ of $L$-rational vectors with $x_w$ equal to the pivot-normalised evaluation vector `evalVec s w` for $w\in\mathrm{supp}\,B'$ and for $w=v_0$, every $t$ with $\mathrm{ord}_{v_0}t=1$ when $B(v_0)>0$, every $a\in L$ equal to the regularised value $\mathrm{evalAt}_{v_0}\!\left(u\,s_{\mathrm{piv}}^{-k}t^{-B(v_0)}\right)$ and every $y$ whose entries are, when $B(v_0)>0$, the corresponding order-one regularised values of the chord functions $\mathrm{evalVec}(v_0)_{p_1}s_{p_2}-\mathrm{evalVec}(v_0)_{p_2}s_{p_1}$ with $\sup_p\nu(y_p)\ne 0$, one has $$\log\nu(a)\le\log\sup_\varphi\nu(c_\varphi)+(k-2B(v_0))\log\sup_i\nu(x_{v_0,i})+B(v_0)\log\sup_p\nu(y_p)-\sum_w B'(w)\,\mathrm{prox}_\nu(x_{v_0},x_w),$$ where $\mathrm{prox}_\nu(x,y)=\log\sup_i\nu(x_i)+\log\sup_i\nu(y_i)-\log\sup_{p}\nu(x_{p_1}y_{p_2}-x_{p_2}y_{p_1})$. The variants are: `hJgood` for finite $\nu$ with $\nu(p)=1$ for all $p$ in some fixed finite set $S$ of primes; `hJbad`, for each finite set $S_0$ with a constant $c_0$, for finite $\nu$ and a prime $p\in S_0$ with $\nu(p)<1$, with the extra term $c_0k(-\log\nu(p))$; `hJarch`, with a constant $c_0$, for infinite $\nu$, with $v_0$ either $\bar\infty$ or a place at which $j$ is integral, and extra term $c_0k$. The conclusion asserts a constant $C$ such that the following holds. Let $u_0,\dots,u_{m+m'-1}$ be non-zero elements with presentations $u_j=\sum_\varphi c_{j\varphi}\prod_l s_{\varphi(l)}$ whose joint normalised logarithmic height is at most $H$; let $B\ge 0$ satisfy $B(w)\le\mathrm{ord}_w(u_j)+k\,E(w)$ for all $j,w$; let moving data $(R_i,t_i,e_i)_{i<m}$ and fixed data $(R'_{i'},t'_{i'},e'_{i'})_{i'<m'}$ be given whose concatenation is a confluent pattern (equal places force equal uniformisers, a place together with an order determines the row, and each $e_i$ is smaller than the number of rows at $R_i$), with $R_i\ne R'_{i'}$ always, no row at $\bar\infty$, $j$ integral at each $R_i$, $B(R_i)=B(R'_{i'})=0$, and $\mathrm{ord}_{R_i}t_i=1$ whenever $e_i>0$ (likewise for the primed data), and assume the determinant of the jet matrix with entries $\mathrm{taylorCoeff}_{R_i}(t_i,e_i)(u_j)$ (respectively for the primed rows) is non-zero. Then $$\tfrac12\sum_i\sum_{i':R_{i'}\ne R_i}b(R_i,R_{i'})+\sum_{i,i'}b(R_i,R'_{i'})+\sum_i\sum_w B(w)\,b(R_i,w)\le\sum_i\Big((k-2e_i)h(R_i)+e_i\,\mathrm{TH}(R_i,t_i)\Big)+\sum_{i'}h\big((\mathrm{taylorCoeff}_{R'_{i'}}(t'_{i'},e'_{i'})(u_j))_j\big)+C,$$ where $h(v)$ is the height of `evalVec s v`, $b(v,w)=h(v)+h(w)-h(\mathrm{chordVec}\,s\,v\,w)$, and $\mathrm{TH}(R_i,t_i)$ is the height of the vector of order-one regularised chord values at $R_i$ with respect to $t_i$.
--
--   This is the many-point form, with confluent jets, of the Jensen inequality (first main theorem) for a frame of sections of $L(kE)$ on $X_0(N)$: the product formula applied to the jet determinant, estimated place by place by the one-point inequalities assumed as `hJgood`, `hJbad` and `hJarch`, yields a bound for the accumulated pair heights of the jet points in terms of their point heights, tangent heights and the heights of the fixed jet rows. It feeds the height-form estimates [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k m m' : ℕ)

    (hJgood : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
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
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w)))
    (hJbad : ∀ S₀ : Finset ℕ, ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
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
            + c₀ * k * (-Real.log (ν (p : ↥L))))
    (hJarch : ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
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
            + c₀ * k)
    (H : ℝ) :
    ∃ C : ℝ, ∀ (u : Fin (m + m') → modularFunctionFieldBar N)
      (c : Fin (m + m') → (Fin k → Fin r) → AlgebraicClosure ℚ),
      (∀ j, u j ≠ 0) → (∀ j, u j = ∑ φ : Fin k → Fin r, c j φ • ∏ l, s (φ l)) →
      absLogHeight (fun q : Fin (m + m') × (Fin k → Fin r) => c q.1 q.2) ≤ H →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, 0 ≤ B w) →
      (∀ j w, B w ≤ w.ord (u j) + ((k : ℤ) • embDivisor N) w) →
      ∀ (R : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : Fin m → modularFunctionFieldBar N) (e : Fin m → ℕ)
        (R' : Fin m' → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t' : Fin m' → modularFunctionFieldBar N) (e' : Fin m' → ℕ),
      IsConfluentPattern (Fin.append R R') (Fin.append t t') (Fin.append e e') →
      (∀ i i', R i ≠ R' i') →
      (∀ i, R i ≠ cuspInftyBar N) → (∀ i', R' i' ≠ cuspInftyBar N) →
      (∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ∈ (R i).toValuationSubring) →
      (∀ i, B (R i) = 0) → (∀ i', B (R' i') = 0) →
      (∀ i, 0 < e i → (R i).ord (t i) = 1) → (∀ i', 0 < e' i' → (R' i').ord (t' i') = 1) →
      IsUnit (jetMatrix (Fin.append R R') (Fin.append t t') (Fin.append e e') u).det →
      (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')) / 2
        + ∑ i : Fin m, ∑ i' : Fin m', pairHt s (R i) (R' i')
        + ∑ i : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
        ≤ ∑ i : Fin m,
            (((k : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
              + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s (R i) (t i) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1)))
          + ∑ i' : Fin m', absLogHeight (fun j : Fin (m + m') => (R' i').taylorCoeff (t' i') (e' i') (u j))
          + C := by sorry
