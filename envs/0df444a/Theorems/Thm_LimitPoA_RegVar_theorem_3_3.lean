-- Prove2me | Theorems.Thm_LimitPoA_RegVar_theorem_3_3
-- name    : LimitPoA.RegVar.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:57.230535+00:00
-- url     : https://prove2.me/theorems/1c18a968-c8e4-4c41-a7e6-1574a2afa5f8
-- title:
--   Theorem 3.3, p. 23 — games with regularly varying cost functions are asymptotically well designed: PoA(d⁽ⁿ⁾) → 1 for every unbounded demand sequence
-- statement:
--   Let $\Gamma$ be a non-atomic congestion game with a finite non-empty set of groups and finitely many resources and strategies, satisfying (2.1), in which every group has a strategy. Suppose every resource cost function $\tau_a$ is non-negative, non-decreasing and continuous on $[0,\infty)$ and regularly varying: for every $x > 0$, $\lim_{t\to\infty}\tau_a(t x)/\tau_a(t)$ exists in $(0,\infty)$. Then $\Gamma$ is asymptotically well designed: for every demand sequence $(d^{(n)})_{n\in\mathbb N}$ with $d^{(n)}_k \ge 0$ and $T(d^{(n)}) = \sum_k d^{(n)}_k \to \infty$,
--   $$\lim_{n\to\infty}\mathrm{PoA}(d^{(n)}) = 1.$$
--
--   This is the main result of the paper. It holds without any growth condition on the demands, and the class of regularly varying costs contains all polynomials with non-negative coefficients, logarithmic factors, and their products and sums; each resource may have a different regular variation index.
--
--   **Formalization Note** The paper assumes $d_k > 0$ for every group; the statement admits zero entries, which the paper's own sequences use and which is equivalent to applying the positive-demand version to every subgame. $\mathrm{PoA}(d)$ is the worst NE cost (`sSup`) over the optimum cost (`sInf`); both sets are non-empty and bounded, so these are genuine values. The "scalable by decomposition" clause of the theorem is a separate milestone.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, p. 23, Theorem 3.3 (proof Appendix A.5, pp. 43–44, with Corollary 3.2)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

namespace LimitPoA.RegVar

/-- Theorem 3.3, p. 23: games with regularly varying cost functions are asymptotically well designed:
`PoA(d^(n)) → 1` along every unbounded demand sequence. -/
theorem theorem_3_3 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a)) :
    IsAsymptoticallyWellDesigned Γ τ := by sorry

end LimitPoA.RegVar
