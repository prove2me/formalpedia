-- Prove2me | Theorems.Thm_HryniewiczCriterion_bounds_global_section_of_approx_of_eventually_czIndex_ge_three
-- name    : HryniewiczCriterion.bounds_global_section_of_approx_of_eventually_czIndex_ge_three
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:33:36.789986+00:00
-- url     : https://prove2.me/theorems/24716359-7470-4505-9000-352eaf0b2ea9
-- title:
--   Non-degenerate approximations fixing an unknotted orbit with $\mathrm{sl}=-1$, whose low-action orbits eventually have index $\ge3$: the orbit eventually bounds a disk-like global section
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $\bar P=(\bar x,\bar T)$ be a prime periodic orbit on $S$ that is unknotted with $\operatorname{sl}(\bar P)=-1$. Let $H_k$ be Hamiltonians such that
--
--   1. every level $H_k^{-1}(1)$ is strictly star-shaped and every $H_k$ is non-degenerate;
--   2. $H_k=H$ and $dH_k=dH$ at every point of $\bar x(\mathbb{R})$;
--   3. $H_k\to H$ in $C^\infty_{\mathrm{loc}}$;
--   4. for every action bound $A$ there is $K$ such that for $k\ge K$ every periodic orbit $R$ on $H_k^{-1}(1)$ with $\mathcal A(R)\le A$ has $\mu_{CZ}(R)\ge3$.
--
--   Then for all large $k$, $\bar P$, viewed as a periodic orbit of $X_{H_k}$ (any $P_k$ with the same parametrization $\bar x$ and period $\bar T$), bounds a disk-like global surface of section for the flow on $H_k^{-1}(1)$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A Hamiltonian $H_k$ is *non-degenerate* when for every periodic orbit $R=(x,T)$ on $H_k^{-1}(1)$ (prime or not) and its linearized flow $Y$, the linearized return map on $\xi$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue. The action of a periodic orbit $R=(x,T)$ is $\mathcal A(R)=\int_0^T\lambda_0(x(t))[\dot x(t)]\,dt$, with $\lambda_0=\tfrac12\sum(q_i\,dp_i-p_i\,dq_i)$ the Liouville form (`liouvilleForm`). The Conley–Zehnder index $\mu_{CZ}(R)$ is `czIndexOfPath` of the linearized flow on $\xi$ written in the global frame $(Z_1,Z_2)$ (`linearizedXiPath`), with its lower semicontinuous extension to degenerate orbits.
--
--   Hypothesis 4 controls only orbits of bounded action, so the levels $H_k^{-1}(1)$ are not assumed dynamically convex, and the limit level $S$ is not assumed dynamically convex or non-degenerate. In Hryniewicz's notation $H_k^{-1}(1)$ carries the non-degenerate contact form $\lambda_k=h_k\lambda$ with $h_k\to1$, $h_k\equiv1$, $dh_k\equiv0$ on $\bar x(\mathbb{R})$ (his (29)). This is the step of his Section 3 that produces disk-like global sections for $\lambda_k$ when $k$ is large.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorems 3.4, 3.10 and 3.11 (pp. 20-25); H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorems 2.2 and 2.5; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012) 1859-1931.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.bounds_global_section_of_approx_of_eventually_czIndex_ge_three (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) (hu : IsUnknotted H P)
    (hsl : HasSelfLinkingNumber H P (-1))
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hnd : (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0))
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y)
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K))
    (hcz : ∀ A : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)),
      IsLinearizedFlow (Hs k) R.x Y → (∫ t in (0 : ℝ)..R.T, liouvilleForm (R.x t) (deriv R.x t)) ≤ A →
      3 ≤ czIndexOfPath (linearizedXiPath (Hs k) R Y)) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      BoundsDiskLikeGlobalSection (Hs k) Pk := by sorry
