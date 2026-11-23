-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_Supplement_theorem_5
-- name    : LargeCongestion.Poisson.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:37:45.563033+00:00
-- url     : https://prove2.me/theorems/3d6ff944-360d-48a4-a099-ce5d00b6a3f9
-- title:
--   Theorem 5 — exact per-resource L² approximation bound for weighted mixed equilibria
-- statement:
--   Let $\Gamma_W$ be a finite weighted congestion game with positive real masses, continuous nonnegative nondecreasing costs $C_e$, and aggregate demands $d_t=\sum_{i:\tau_i=t}w_i$ with $\sum_td_t\le d_{\max}$. Assume $c'_{\max}\ge c'_{\min}>0$ and
--   $$c'_{\min}\le C'_e(x)\le c'_{\max}\qquad(0\le x\le d_{\max}),$$
--   and assume the derivatives are $L$-Lipschitz on that interval, with $L\ge0$. Choose $\kappa$ at least every strategy cardinality, and define exactly as in (31)
--   $$\theta=\sqrt{d_{\max}/4}+\sqrt{\kappa d_{\max}(2c'_{\max}+Ld_{\max}/4)/c'_{\min}}.$$
--   For any independent mixed Nash equilibrium $\hat\sigma$, and any Wardrop pair $(\hat y,\hat x)$ of the nonatomic game with the same aggregate demands, every resource satisfies
--   $$\|X_e-\hat x_e\|_{L^2}\le\theta\sqrt{w},\qquad w=\max_iw_i.$$
--   The Wardrop load vector is unique: every Wardrop pair at these demands has the same resource vector. The L² norm is $\sqrt{\mathbb E[(X_e-\hat x_e)^2]}$ under the mixed profile. This is a finite-game quantitative companion to Theorem 1, with the source's full constant.
--
--   Differences from the source:
--   - reading: printed blackboard N glyphs in weighted costs and weights (pp. 9–10) → positive real weights and nonnegative continuous real-load costs; reason: (12) requires positive weights tending to zero, and the continuous derivatives in Section 6 use real loads
--   - encoding: finite players and resource-subset mixed strategies → players Fin N and probability vectors on Finset E, zero off S_t; reason: enumeration changes no finite game; nonempty strategy families are the standing strategy-existence convention
--   - encoding: derivatives C_e prime on [0,d_max] → explicit D_e with HasDerivWithinAt on the closed interval; reason: these are the same derivatives on the interior with one-sided endpoint values; no derivative outside the stated interval is required
--   - encoding: the unique Wardrop resource load vector → a Wardrop pair is given and uniqueness of its load vector is concluded alongside the bound; reason: the source calls this load unique; uniqueness is not added as a premise
--   - encoding: scalar random-variable L2 error and maximum player mass → sqrt of the finite product-law expectation of squared error, and finite real supremum with empty maximum zero; reason: these give the stated L2 error and usual maximum whenever players exist; no player or resource nonemptiness is added
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, Theorem 5, p. 25

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Approximation
import Definitions.Def_LargeCongestion_Poisson_Supplement_Norms

namespace LargeCongestion.Poisson.Supplement

theorem theorem_5 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    {N : ℕ} (G : WeightedGame E T N) (hG : G.Admissible)
    (D : E → ℝ → ℝ) (dmax cmin cmax L κ : ℝ)
    (hd : ∑ t, G.demands t ≤ dmax) (hmin : 0 < cmin) (hmax : cmin ≤ cmax)
    (hL : 0 ≤ L) (hderiv : HasCostDerivative G.cost D dmax)
    (hbounds : ∀ e x, x ∈ Set.Icc 0 dmax → cmin ≤ D e x ∧ D e x ≤ cmax)
    (hlip : ∀ e x z, x ∈ Set.Icc 0 dmax → z ∈ Set.Icc 0 dmax →
      |D e x - D e z| ≤ L * |x - z|)
    (hκ : ∀ t, ∀ s ∈ G.strategies t, (s.card : ℝ) ≤ κ)
    (σ : Fin N → Finset E → ℝ) (hσ : G.IsMNE σ)
    (yhat : T → Finset E → ℝ) (xhat : E → ℝ)
    (heq : IsWardrop G.strategies G.cost G.demands yhat xhat) :
    (∀ e, wL2Error G.mass σ e (xhat e) ≤ theta dmax cmin cmax L κ * Real.sqrt (maxU G.mass)) ∧
    ∀ y' x', IsWardrop G.strategies G.cost G.demands y' x' → x' = xhat := by sorry

end LargeCongestion.Poisson.Supplement
