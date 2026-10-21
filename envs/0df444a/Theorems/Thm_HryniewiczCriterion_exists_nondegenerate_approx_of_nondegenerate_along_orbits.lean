-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_nondegenerate_approx_of_nondegenerate_along_orbits
-- name    : HryniewiczCriterion.exists_nondegenerate_approx_of_nondegenerate_along_orbits
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:56:14.848403+00:00
-- url     : https://prove2.me/theorems/6377f11e-1a99-4185-afaf-f32dd06acbe8
-- title:
--   Non-degenerate approximations of a star-shaped Hamiltonian, agreeing with it to first order along two given non-degenerate periodic orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $P=(x_P,T_P)$, $Q=(x_Q,T_Q)$ be periodic orbits of $X_H$ on $S$ such that every periodic orbit of $X_H$ on $S$ whose image lies in $x_P(\mathbb{R})\cup x_Q(\mathbb{R})$ (that is, $P$, $Q$ and all their iterates) is non-degenerate. Then there is a sequence of Hamiltonians $H_k:\mathbb{R}^4\to\mathbb{R}$ such that
--
--   1. every level $H_k^{-1}(1)$ is strictly star-shaped;
--   2. every $H_k$ is non-degenerate: every periodic orbit of $X_{H_k}$ on $H_k^{-1}(1)$, prime or multiply covered, is non-degenerate;
--   3. $H_k=H$ and $dH_k=dH$ at every point of $x_P(\mathbb{R})\cup x_Q(\mathbb{R})$;
--   4. $H_k\to H$ in $C^\infty_{\mathrm{loc}}$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A periodic orbit $R=(x,T)$ on $H^{-1}(1)$ (prime or not) is *non-degenerate* when, for its linearized flow $Y$, the linearized return map on $\xi=TS/\mathbb{R}X_{H}$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue. A Hamiltonian is non-degenerate when all its periodic orbits on the level $1$ are.
--
--   Only the orbits $P$ and $Q$ are assumed non-degenerate; the other periodic orbits of $X_H$ may be degenerate. In contact language this is the density, relative to a prescribed $1$-jet along two non-degenerate closed orbits, of non-degenerate contact forms $g\lambda$ near $\lambda$ (Kupka–Smale for Reeb flows).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, (28)-(29) on p. 20 (the set $\mathcal F$ of non-degenerate forms is residual) and the proof of Lemma 3.12, p. 26.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_nondegenerate_approx_of_nondegenerate_along_orbits (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H)
    (hPQ : ∀ (R : PeriodicOrbit H), R.image ⊆ P.image ∪ Q.image →
      ∀ (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow H R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath H R Y 1).mulVec v = v → v = 0) :
    ∃ Hs : ℕ → R4 → ℝ, (∀ k, IsStrictlyStarShapedLevel (Hs k)) ∧
      (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0) ∧
      (∀ k, ∀ y ∈ P.image ∪ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y) ∧
      (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K) := by sorry
