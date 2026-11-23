-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_Supplement_proposition_2
-- name    : LargeCongestion.Poisson.Supplement.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:37:07.193458+00:00
-- url     : https://prove2.me/theorems/fe65b8a8-9ee2-4990-ac9b-71cc468b963d
-- title:
--   Proposition 2 — both Euclidean load bounds for approximate equilibrium and perturbed demand
-- statement:
--   Fix a finite nonatomic congestion structure with continuous nonnegative nondecreasing real-load costs $C_e$, and a Wardrop equilibrium $(\hat y,\hat x)$ at demands $d$. Suppose $\sum_td_t\le d_{\max}$, and the derivatives satisfy $C'_e(x)\ge c'_{\min}>0$ for every resource and $x\in[0,d_{\max}]$. Let $B\ge\sum_{e\in s}C_e(d_{\max})$ for every feasible strategy, and set $\Xi=\sqrt{2B/c'_{\min}}$.
--
--   Both conclusions of Proposition 2 hold:
--
--   1. For every additive $\varepsilon$-Wardrop feasible pair $(y,x)$ at the same demands,
--   $$\|x-\hat x\|_2\le\sqrt{\varepsilon d_{\max}/c'_{\min}}.$$
--   2. For every Wardrop pair $(y',x')$ at perturbed demands $d'$ with $\sum_td'_t\le d_{\max}$,
--   $$\|x'-\hat x\|_2\le\Xi\sqrt{\|d'-d\|_1}.$$
--
--   The norms are the Euclidean norm of the full resource vector and the sum of absolute type-demand differences. Part (a) supports Theorem 5; part (b) is retained in the same item, including zero type demands.
--
--   Differences from the source:
--   - reading: continuous congestion-cost domains in the standing structure → nonnegative real loads and real costs; reason: the derivatives and the nonatomic model require the real-load interpretation
--   - encoding: derivatives C_e prime on [0,d_max] → explicit D_e with HasDerivWithinAt on the closed interval; reason: these are the same derivatives on the interior with one-sided endpoint values; no derivative outside the stated interval is required
--   - encoding: epsilon-approximate equilibrium → nonnegative epsilon and the feasible-pair condition (30); reason: epsilon is an additive approximation tolerance; negative tolerances are outside that convention
--   - encoding: Euclidean and l1 norms, constant C bounding strategy costs → explicit square-root-of-squares and absolute-sum norms, and the constant named B; reason: this avoids the default sup norm on function types and distinguishes the scalar bound from the cost family
--   - encoding: finite strategy families → the standing nonempty-strategy convention is explicit; reason: this supplies the same feasible-strategy objects used by Wardrop equilibria
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, Proposition 2, p. 24

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Approximation
import Definitions.Def_LargeCongestion_Poisson_Supplement_Norms

namespace LargeCongestion.Poisson.Supplement

theorem proposition_2 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (C D : E → ℝ → ℝ)
    (hS : StrategiesNonempty S) (hC : ContinuousCosts C)
    (d : T → ℝ) (yhat : T → Finset E → ℝ) (xhat : E → ℝ)
    (heq : IsWardrop S C d yhat xhat) (dmax cmin B : ℝ)
    (hd : ∑ t, d t ≤ dmax) (hcmin : 0 < cmin)
    (hderiv : HasCostDerivative C D dmax)
    (hlower : ∀ e x, x ∈ Set.Icc 0 dmax → cmin ≤ D e x)
    (hB : ∀ t, ∀ s ∈ S t, ∑ e ∈ s, C e dmax ≤ B) :
    (∀ (ε : ℝ) (y : T → Finset E → ℝ) (x : E → ℝ), IsEpsWardrop S C d ε y x →
      loadNorm (fun e => x e - xhat e) ≤ Real.sqrt (ε * dmax / cmin)) ∧
    (∀ (d' : T → ℝ) (y' : T → Finset E → ℝ) (x' : E → ℝ),
      IsWardrop S C d' y' x' → (∑ t, d' t) ≤ dmax →
      loadNorm (fun e => x' e - xhat e) ≤
        Real.sqrt (2 * B / cmin) * Real.sqrt (demandDistance d d')) := by sorry

end LargeCongestion.Poisson.Supplement
