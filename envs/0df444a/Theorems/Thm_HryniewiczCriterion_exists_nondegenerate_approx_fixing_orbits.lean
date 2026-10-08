-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_nondegenerate_approx_fixing_orbits
-- name    : HryniewiczCriterion.exists_nondegenerate_approx_fixing_orbits
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-08T09:48:35.553984+00:00
-- url     : https://prove2.me/theorems/d0cf6d59-0b29-46b9-bc2b-0eb5393408af
-- title:
--   Non-degenerate approximations of a star-shaped Hamiltonian that agree with it to first order along two given periodic orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $P=(x_P,T_P)$, $Q=(x_Q,T_Q)$ be periodic orbits of $X_H$ on $S$. Then there is a sequence of Hamiltonians $H_k:\mathbb{R}^4\to\mathbb{R}$ such that
--
--   1. every level $H_k^{-1}(1)$ is strictly star-shaped;
--   2. every $H_k$ is non-degenerate: no periodic orbit of $X_{H_k}$ on $H_k^{-1}(1)$, prime or multiply covered, has $1$ as a Floquet multiplier of its linearized return map on $\xi$;
--   3. $H_k=H$ and $dH_k=dH$ at every point of $x_P(\mathbb{R})\cup x_Q(\mathbb{R})$;
--   4. $H_k\to H$ in $C^\infty_{\mathrm{loc}}$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A Hamiltonian $H_k$ is *non-degenerate* when for every periodic orbit $R=(x,T)$ on $H_k^{-1}(1)$ (prime or not) and its linearized flow $Y$, the linearized return map on $\xi=TS/\mathbb{R}X_{H_k}$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue.
--
--   By (3), $X_{H_k}=X_H$ along both orbits, so $P$ and $Q$ stay periodic orbits of every $X_{H_k}$. Only the $2$-jet transverse to the orbits is changed, which is what makes $P$ and $Q$ themselves non-degenerate.
--
--   In contact language, $H_k^{-1}(1)$ corresponds to the form $g_k\lambda$ on $S^3$ with $g_k\to1$ in $C^\infty$ and $g_k\equiv1$, $dg_k\equiv0$ on the two orbits. Non-degenerate forms are residual in $C^\infty$ (Kupka–Smale for Reeb flows), and the residual set can be chosen inside the forms with a prescribed $1$-jet along finitely many closed orbits. This is the perturbation used in the proof of Lemma 3.12 of Hryniewicz (2014).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Section 3.3, proof of Lemma 3.12 (p. 26: the sequence $g_k$) and (28)-(29) on p. 20 (the set $\mathcal F$ of non-degenerate forms is residual).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_nondegenerate_approx_fixing_orbits (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H) :
    ∃ Hs : ℕ → R4 → ℝ, (∀ k, IsStrictlyStarShapedLevel (Hs k)) ∧
      (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0) ∧
      (∀ k, ∀ y ∈ P.image ∪ Q.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y) ∧
      (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K) := by sorry
