-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_proposition_F_3
-- name    : OrderSelProphet.Kernel.proposition_F_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:00:13.021211+00:00
-- url     : https://prove2.me/theorems/17064059-5a67-4215-b292-ab043bd793b6
-- title:
--   Proposition F.3 — direct regional comparison: the recursion (117) gives $V_\lambda(r_j)\le v_j$ on $\Lambda(\mathcal R)$, and $\bar\ell_\lambda\le\Gamma_1+v_0$ if $r_0=0$
-- statement:
--   Fix a parameter box $\mathcal R$. Let $0\le r_0<r_1<\dots<r_N<\infty$, and suppose $v_N\ge0$ satisfies $V_\lambda(r_N)\le v_N$ for every $\lambda\in\Lambda(\mathcal R)$. Suppose that for $j=N-1,\dots,0$ there is a uniform upper bound $R_j(r)\ge R(r)$ on $[r_j,r_{j+1}]$ (for every $\lambda\in\Lambda(\mathcal R)$) and numbers $H_j$ and $\kappa_j\ge0$ such that
--   $$\frac{(r-k)R_j(r)}{D(r)^2}-\frac{k\,v_{j+1}}{D(r)}\le H_j,\qquad\frac{k}{D(r)}\le\kappa_j\quad(116)$$
--   throughout the admissible mass and state ranges on that interval, i.e. for $r\in[r_j,r_{j+1}]$, $(x,h)\in\mathcal D_{\mathcal R}(r)$ and $k=h+\nu(r;x)$. Choose recursively
--   $$v_j\ge\max\Big\{0,\ v_{j+1}+\begin{cases}(r_{j+1}-r_j)H_j,&H_j\ge0,\\ \frac{(r_{j+1}-r_j)H_j}{1+(r_{j+1}-r_j)\kappa_j},&H_j<0.\end{cases}\Big\}\quad(117)$$
--   Then $V_\lambda(r_j)\le v_j$ for $j=0,\dots,N$ and every $\lambda\in\Lambda(\mathcal R)$. If $r_0=0$, then $\bar\ell_\lambda\le\Gamma_1+v_0$ (118).
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: (116) 'throughout the admissible mass and state ranges on that interval' → for every r ∈ [r_j, r_{j+1}] and every (x, h) ∈ D_R(r) (Admissible), with k = h + ν(r; x); reason: D_R(r) (104) is the paper's admissible set and k = h + ν (98)
--   - encoding: a uniform upper bound R_j(r) ≥ R(r) on [r_j, r_{j+1}] → functions Rb j : ℝ → ℝ with R_λ(r) ≤ Rb j r for every λ ∈ Λ(R) and r ∈ [r_j, r_{j+1}]; reason: 'uniform' over the region
--   - encoding: grid r_0 < ⋯ < r_N, numbers v_j, H_j, κ_j, ℓ̄_λ ≤ Γ1 + v_0 → sequences ℕ → ℝ constrained for j ≤ N; auxLoad ≤ ENNReal.ofReal(Γ1 + v 0); reason: indexing convention; loads in ℝ≥0∞
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Proposition F.3, p. 54

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Proposition F.3 (Direct regional comparison), p. 54. Grid `r_0 < ⋯ < r_N`, bounds `v_j`,
uniform upper bounds `R_j` of `R`, numbers `H_j`, `κ_j` on a parameter box. -/
theorem proposition_F_3 (R : ParamBox) (hR : R.Valid) (N : ℕ) (rs v H κ : ℕ → ℝ)
    (Rb : ℕ → ℝ → ℝ) (hr0 : 0 ≤ rs 0) (hrs : ∀ j < N, rs j < rs (j + 1)) (hvN : 0 ≤ v N)
    (hVN : ∀ lam : Profile, InRegion R lam.1 → contV lam.1 (rs N) ≤ v N)
    (hRb : ∀ j < N, ∀ lam : Profile, InRegion R lam.1 →
      ∀ r ∈ Icc (rs j) (rs (j + 1)), Rc lam.1 r ≤ Rb j r)
    (hκ : ∀ j < N, 0 ≤ κ j)
    (h116 : ∀ j < N, ∀ r ∈ Icc (rs j) (rs (j + 1)), ∀ (x : Fin 4 → ℝ) (h : ℝ), Admissible R r x h →
      (r - (h + nuR r x)) * Rb j r / Dc r ^ 2 - (h + nuR r x) * v (j + 1) / Dc r ≤ H j ∧
        (h + nuR r x) / Dc r ≤ κ j)
    (h117 : ∀ j < N, max 0 (v (j + 1) +
      (if 0 ≤ H j then (rs (j + 1) - rs j) * H j
        else (rs (j + 1) - rs j) * H j / (1 + (rs (j + 1) - rs j) * κ j))) ≤ v j) :
    (∀ lam : Profile, InRegion R lam.1 → ∀ j ≤ N, contV lam.1 (rs j) ≤ v j) ∧
      (rs 0 = 0 → ∀ lam : Profile, InRegion R lam.1 →
        auxLoad lam.1 ≤ ENNReal.ofReal (Gamma1 + v 0)) := by sorry

end OrderSelProphet.Kernel
