-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_seq_tendsto_place
-- name    : ModularCurve.JZero.exists_seq_tendsto_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/479598fa-2c39-521e-8ed6-97fa25c2b185
-- title:
--   Approach to a base point: limits of archimedean chordal terms
-- statement:
--   Fix $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\bar{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series. Let $s = (s_i)_{i<r}$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\bar{\mathbb Q}$ and spans the Riemann–Roch space of $E :=$ `embDivisor N` $= (\mathrm{embDegree}\,N)\cdot \bar\infty$, where $\bar\infty =$ `cuspInftyBar N`; for a place $v$ write $x_v :=$ `evalVec s v`, the vector with entries $v(s_i/s_{\mathrm{piv}(v)})$. Let $v_0$ be a place with a $t \in \bar F_N$ of order $\mathrm{ord}_{v_0} t = 1$, and assume either $v_0 = \bar\infty$ or that the element of $\bar F_N$ given by the coefficientwise image of the $q$-expansion $j$ lies in the valuation subring of $v_0$. Then for every ring homomorphism $\sigma \colon \bar{\mathbb Q} \to \mathbb C$, every finite set $S$ of places, every $k \in \mathbb N$, every nonzero $u$ in the Riemann–Roch space of $k\cdot E$ and every $e \in \mathbb N$ with $e = \mathrm{ord}_{v_0} u + k\,E(v_0)$, there is a sequence of places $v_n$, none in $S$ and none equal to $v_0$, such that: for each $w \in S$ with $w \ne v_0$ the chordal proximity $\mathrm{prox}(x_{v_n}, x_w)$ converges to $\mathrm{prox}(x_{v_0},x_w)$, where $\mathrm{prox}(x,y) = \log \sup_i \|\sigma x_i\| + \log \sup_j \|\sigma y_j\| - \log \sup_{p,q} \|\sigma(x_p y_q - x_q y_p)\|$; and
--   $$k \log \sup_i \|\sigma x_{v_n,i}\| - \log \|\sigma\,\mathrm{secVal}(s,v_n,k,u)\| - e\,\mathrm{prox}(x_{v_n},x_{v_0})$$
--   converges to
--   $$(k-2e)\log \sup_i\|\sigma x_{v_0,i}\| + e \log \sup_{i,j} \|\sigma\,\mathrm{regVal}(s,v_0,t,1,1, x_{v_0,i}\,s_j - x_{v_0,j}\,s_i)\| - \log \|\sigma\,\mathrm{regVal}(s,v_0,t,k,e,u)\|,$$
--   where $\mathrm{secVal}(s,v,k,u) = v(u\, s_{\mathrm{piv}(v)}^{-k})$ and $\mathrm{regVal}(s,v,t,k,e,u) = v(u\,s_{\mathrm{piv}(v)}^{-k} t^{-e})$ (both $0$ when $r = 0$).
--
--   This is the approach lemma at a base point of $X_0(N)$: the archimedean local contribution at a point of the divisor support is realised as an exact limit of the corresponding generic-point expression along algebraic points tending to $v_0$, the $e\log|t|$ singularities of the section value and of the proximity term cancelling to leave the regularised tangent datum. It is used in the derivation of the archimedean Jensen identity at non-cuspidal points, by [`ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal`](thm.html#ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal) and [`ModularCurve.JZero.jensen_arch_at_of_nonCuspidal`](thm.html#ModularCurve.JZero.jensen_arch_at_of_nonCuspidal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_seq_tendsto_place.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_seq_tendsto_place (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (ht : v₀.ord t = 1)
    (hv₀ : v₀ = cuspInftyBar N ∨
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ v₀.toValuationSubring) :
    ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
      (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ e : ℕ, (e : ℤ) = v₀.ord u + k * embDivisor N v₀ →
      ∃ v : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
        (∀ w ∈ S, w ≠ v₀ →
          Filter.Tendsto (fun n => prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w))
            Filter.atTop (nhds (prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w)))) ∧
        Filter.Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖)
            - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s v₀))
          Filter.atTop (nhds (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
            + (e : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1))‖)
            - Real.log ‖σ (regVal s v₀ t k e u)‖)) := by sorry
