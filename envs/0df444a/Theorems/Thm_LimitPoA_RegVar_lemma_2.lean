-- Prove2me | Theorems.Thm_LimitPoA_RegVar_lemma_2
-- name    : LimitPoA.RegVar.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:35.662788+00:00
-- url     : https://prove2.me/theorems/baaac852-df7f-4785-9751-49e98b430a1b
-- title:
--   Lemma 2, p. 11 — scaling a game by g > 0 leaves the PoA unchanged: PoA(d) = PoA^[g](d/T(d))
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game satisfying the standing assumptions, whose cost functions $\tau_a$ are non-negative, non-decreasing and continuous on $[0,\infty)$ and not identically zero on $(0,\infty)$. Let $d \ge 0$ be a demand vector with total demand $T(d) > 0$, and let $g > 0$. Let $\Gamma^{[g]}$ be the scaled game, with cost functions $\tau^{[g]}_a(x) = \tau_a(T(d)\cdot x)/g$ and demand vector $d/T(d)$. Then
--   $$\mathrm{PoA}(d) = \mathrm{PoA}^{[g]}\!\left(\frac{d}{T(d)}\right),$$
--   where $\mathrm{PoA}^{[g]}$ is the price of anarchy of $\Gamma^{[g]}$.
--
--   Scaling therefore lets the limit analysis of $\mathrm{PoA}(d^{(n)})$ be carried out on games of total demand 1.
--
--   **Formalization Note** The scaled costs are defined on all of $\mathbb R$; for demand $d/T(d)$ only consumption rates in $[0,1]$ are evaluated, which is where Definition 3.1 defines them.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 11, Lemma 2 (with Definition 3.1)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

namespace LimitPoA.RegVar

open Filter Topology

/-- Lemma 2, p. 11: scaling by `g > 0` leaves the PoA unchanged, `PoA(d) = PoA^[g](d/T(d))`. -/
theorem lemma_2 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (g : ℝ) (hg : 0 < g) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand Γ d) :
    PoA Γ τ d =
      PoA Γ (scaled Γ τ (totalDemand Γ d) g) (fun k => d k / totalDemand Γ d) := by sorry

end LimitPoA.RegVar
