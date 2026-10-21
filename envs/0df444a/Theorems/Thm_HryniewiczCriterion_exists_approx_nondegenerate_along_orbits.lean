-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_approx_nondegenerate_along_orbits
-- name    : HryniewiczCriterion.exists_approx_nondegenerate_along_orbits
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:56:14.285403+00:00
-- url     : https://prove2.me/theorems/20847182-2d3b-4c6b-a5b2-4964e9205203
-- title:
--   Star-shaped approximations of a Hamiltonian, agreeing with it to first order along two periodic orbits, for which these orbits and all their iterates are non-degenerate
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $P=(x_P,T_P)$, $Q=(x_Q,T_Q)$ be periodic orbits of $X_H$ on $S$. Then there is a sequence of Hamiltonians $H_k:\mathbb{R}^4\to\mathbb{R}$ such that
--
--   1. every level $H_k^{-1}(1)$ is strictly star-shaped;
--   2. every periodic orbit $R$ of $X_{H_k}$ on $H_k^{-1}(1)$ whose image lies in $x_P(\mathbb{R})\cup x_Q(\mathbb{R})$ (that is, $P$, $Q$ and all their iterates, with any time shift) is non-degenerate;
--   3. $H_k=H$ and $dH_k=dH$ at every point of $x_P(\mathbb{R})\cup x_Q(\mathbb{R})$;
--   4. $H_k\to H$ in $C^\infty_{\mathrm{loc}}$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A periodic orbit $R=(x,T)$ on $H^{-1}(1)$ (prime or not) is *non-degenerate* when, for its linearized flow $Y$, the linearized return map on $\xi=TS/\mathbb{R}X_{H}$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue. A Hamiltonian is non-degenerate when all its periodic orbits on the level $1$ are.
--
--   By (3), $X_{H_k}=X_H$ along both orbits, so $P$ and $Q$ stay periodic orbits of every $X_{H_k}$. Nothing is asserted about the other periodic orbits of $X_{H_k}$. In contact language: $H_k^{-1}(1)$ carries $g_k\lambda$ with $g_k\to1$ in $C^\infty$, $g_k\equiv1$ and $dg_k\equiv0$ on the two orbits, and the two orbits are non-degenerate for $g_k\lambda$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Section 3.3, proof of Lemma 3.12 (p. 26: the sequence $g_k$), and (28)-(29) on p. 20.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_approx_nondegenerate_along_orbits (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H) :
    ∃ Hs : ℕ → R4 → ℝ, (∀ k, IsStrictlyStarShapedLevel (Hs k)) ∧
      (∀ k (R : PeriodicOrbit (Hs k)), R.image ⊆ P.image ∪ Q.image →
      ∀ (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0) ∧
      (∀ k, ∀ y ∈ P.image ∪ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y) ∧
      (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K) := by sorry
