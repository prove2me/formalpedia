-- Prove2me | Theorems.Thm_HryniewiczCriterion_bounds_global_section_of_nondegenerate_approx
-- name    : HryniewiczCriterion.bounds_global_section_of_nondegenerate_approx
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-08T09:48:41.122523+00:00
-- url     : https://prove2.me/theorems/9075f533-a475-42ee-a512-bcb3eed50e4f
-- title:
--   Hryniewicz §3.2–3.3: along non-degenerate approximations that fix the binding to first order, $\bar P$ eventually bounds a disk-like global section
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level with dynamically convex flow, and let $\bar P=(\bar x,\bar T)$ be a prime periodic orbit on $S$ that is unknotted with $\operatorname{sl}(\bar P)=-1$. Let $H_k$ be Hamiltonians with strictly star-shaped levels $H_k^{-1}(1)$, each non-degenerate, with $H_k=H$ and $dH_k=dH$ on $\bar x(\mathbb{R})$, and with $H_k\to H$ in $C^\infty_{\mathrm{loc}}$. Then for all large $k$, $\bar P$, viewed as a periodic orbit of $X_{H_k}$, bounds a disk-like global surface of section for the flow on $H_k^{-1}(1)$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A Hamiltonian $H_k$ is *non-degenerate* when for every periodic orbit $R=(x,T)$ on $H_k^{-1}(1)$ (prime or not) and its linearized flow $Y$, the linearized return map on $\xi=TS/\mathbb{R}X_{H_k}$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue.
--
--   In Hryniewicz's notation $H_k^{-1}(1)$ carries the non-degenerate contact form $\lambda_k=h_k\lambda$ with $h_k\to1$, $h_k\equiv1$, $dh_k\equiv0$ on $\bar x(\mathbb{R})$ (his (29)). The statement combines three results for $k$ large:
--
--   - Theorem 3.4: there is an embedded fast finite-energy plane asymptotic to $\bar P$. It is built from a spanning disk with $\operatorname{sl}=-1$ (Lemma 3.3), Bishop families, and dynamical convexity of $\lambda$, which passes to orbits of $\lambda_k$ with bounded action.
--   - Theorem 3.10: compactness of the normalized fast planes.
--   - Theorem 3.11 (HWZ, Theorem 2.5 of the 1998 paper): these planes form an open book with binding $\bar P$ whose pages are global surfaces of section.
--
--   The closure of any page is the required disk.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorems 3.4, 3.10 and 3.11 (pp. 20-25) and the proof of Lemma 3.12 (p. 26); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorems 2.2 and 2.5; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012) 1859-1931.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.bounds_global_section_of_nondegenerate_approx (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) (hu : IsUnknotted H P)
    (hsl : HasSelfLinkingNumber H P (-1))
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hnd : (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0))
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y)
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K)) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      BoundsDiskLikeGlobalSection (Hs k) Pk := by sorry
