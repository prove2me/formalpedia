-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_seq_tendsto_cuspInftyBar
-- name    : ModularCurve.JZero.exists_seq_tendsto_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9c7a1233-bdbe-51ab-bba4-cba5a1d60a57
-- title:
--   Places approaching the base cusp: proximities and section sizes
-- statement:
--   Fix $N \ge 1$ and work in $\bar F_N :=$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, realised inside Laurent series over $\overline{\mathbb Q}$; let $\bar\infty :=$ `cuspInftyBar N` be its distinguished $q$-expansion place. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space $\{f : v(f) \le \exp(D v) \text{ for all places } v\}$ of $D =$ `embDivisor N` $= (2g+1)\,\bar\infty$, where $2g+1 =$ `embDegree N` and $g$ is `genusFF` of $\bar F_N$; and let $t \in \bar F_N$ have $\mathrm{ord}_{\bar\infty}(t) = 1$. The assertion is the existence of a real $\kappa_0$ such that for every ring homomorphism $\sigma : \overline{\mathbb Q} \to \mathbb C$, every finite set $S$ of places of $\bar F_N$ over $\overline{\mathbb Q}$, every $k \in \mathbb N$, every nonzero $u$ in the Riemann–Roch space of $k \cdot D$, and every $e \in \mathbb N$ with $e = \mathrm{ord}_{\bar\infty}(u) + k(2g+1)$ as integers, there are a real $\kappa$ with $|\kappa| \le \kappa_0$ and a sequence of places $v_n \notin S$ with the following two convergences, where $\mathrm{prox}$ is the chordal proximity $\mathrm{prox}(x,y) = \log \sup_i \|\sigma(x_i)\| + \log \sup_i \|\sigma(y_i)\| - \log \sup_{i,j} \|\sigma(x_i y_j - x_j y_i)\|$ of the pivot-normalised coordinate vectors `evalVec s v` $= (v(s_i/s_{\mathrm{piv}(v)}))_i$. First, for each $w \in S$ with $w \ne \bar\infty$, $\mathrm{prox}(\mathrm{evalVec}\,s\,v_n, \mathrm{evalVec}\,s\,w) \to \mathrm{prox}(\mathrm{evalVec}\,s\,\bar\infty, \mathrm{evalVec}\,s\,w)$. Second, $$k\log \sup_i \|\sigma(\mathrm{evalVec}\,s\,v_n\,i)\| - \log\|\sigma(\mathrm{secVal}\,s\,v_n\,k\,u)\| - e\,\mathrm{prox}(\mathrm{evalVec}\,s\,v_n, \mathrm{evalVec}\,s\,\bar\infty)$$ converges to $k\log \sup_i \|\sigma(\mathrm{evalVec}\,s\,\bar\infty\,i)\| - \log\|\sigma(\mathrm{regVal}\,s\,\bar\infty\,t\,k\,e\,u)\| + e\kappa$, where $\mathrm{secVal}\,s\,v\,k\,u = v(u\,s_{\mathrm{piv}(v)}^{-k})$ and $\mathrm{regVal}\,s\,\bar\infty\,t\,k\,e\,u = \bar\infty(u\,s_{\mathrm{piv}(\bar\infty)}^{-k}\,t^{-e})$ are the pivot-trivialised value of $u$ at $v$ and its $t^{e}$-regularised value at the cusp. The bound $\kappa_0$ is uniform in $\sigma$, $S$, $k$, $u$ and $e$, depending only on $N$, $s$ and $t$.
--
--   This is the local approach statement at the base cusp of $X_0(N)$: along a suitable sequence of places avoiding a prescribed finite set, chordal proximities to fixed points converge to their values at the cusp, and the $e$-normalised logarithmic size of a section of $kE$ converges to the size of its regularised value at the cusp, up to a defect $e\kappa$ with $|\kappa|$ bounded in terms of the curve, the basis and the uniformiser alone. It feeds the cusp case of the height-form computation on $J_0(N)$, being cited by [`ModularCurve.JZero.chowSide_cusp_of_off_support`](thm.html#ModularCurve.JZero.chowSide_cusp_of_off_support).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_seq_tendsto_cuspInftyBar.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_seq_tendsto_cuspInftyBar (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ κ₀ : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ)
      (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
      (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ e : ℕ, (e : ℤ) = (cuspInftyBar N).ord u + k * embDegree N →
      ∃ (κ : ℝ) (v : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        |κ| ≤ κ₀ ∧ (∀ n, v n ∉ S) ∧
        (∀ w ∈ S, w ≠ cuspInftyBar N →
          Filter.Tendsto (fun n => prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w))
            Filter.atTop (nhds (prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w)))) ∧
        Filter.Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖)
            - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s (cuspInftyBar N)))
          Filter.atTop (nhds ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
            - Real.log ‖σ (regVal s (cuspInftyBar N) t k e u)‖ + (e : ℝ) * κ)) := by sorry
