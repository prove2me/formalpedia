-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_prime_periodicOrbit_cover
-- name    : HryniewiczCriterion.exists_prime_periodicOrbit_cover
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T17:59:15.330317+00:00
-- url     : https://prove2.me/theorems/5597d5f2-7258-4e7b-8915-de2e11f9f265
-- title:
--   Every periodic orbit on a star-shaped level is a finite cover of a prime periodic orbit with the same trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $Q=(x,T)$ a periodic orbit of $X_H$ on $S$. Then $x$ has a least positive period $T_0$, and $T=kT_0$ for some integer $k\ge1$. In other words, $Q_0=(x,T_0)$ is a prime periodic orbit and $Q$ is its $k$-fold cover.
--
--   Proof idea. The periods of $x$ form an additive subgroup $G\subset\mathbb{R}$ containing $T>0$. If $G$ were dense, continuity would make $x$ constant, so $X_H(x)=x'=0$. But $X_H\neq0$ on $S$, because $dH(x)\,x>0$ there. So $G=\mathbb{Z}T_0$ is cyclic with $T_0>0$. A return $x(t)=x(0)$ with $0<t<T_0$ would make $t$ a period, by uniqueness of solutions of $\dot y=X_H(y)$, which contradicts minimality.
-- source:
--   Standard (periods of a non-constant continuous function form a discrete subgroup of $\mathbb{R}$); used implicitly in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, §1 (prime vs. multiply covered orbits).

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_prime_periodicOrbit_cover (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (Q : PeriodicOrbit H) :
    ∃ Q₀ : PeriodicOrbit H, Q₀.IsPrime ∧ Q₀.x = Q.x ∧ ∃ k : ℕ, 0 < k ∧ Q.T = k * Q₀.T := by sorry
