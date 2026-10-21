-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_transverse_disk_open_book_of_approx
-- name    : HryniewiczCriterion.exists_transverse_disk_open_book_of_approx
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:53:05.401807+00:00
-- url     : https://prove2.me/theorems/a8acd2b5-4acc-4abe-a65d-aa3b431e3f9e
-- title:
--   Non-degenerate approximations fixing an unknotted orbit with $\mathrm{sl}=-1$, whose low-action orbits eventually have index $\ge3$: the orbit eventually binds a transverse disk open book
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and let $\bar P=(\bar x,\bar T)$ be a prime periodic orbit on $S$ that is unknotted with $\operatorname{sl}(\bar P)=-1$. Let $H_k$ be Hamiltonians such that
--
--   1. every level $H_k^{-1}(1)$ is strictly star-shaped and every $H_k$ is non-degenerate;
--   2. $H_k=H$ and $dH_k=dH$ at every point of $\bar x(\mathbb{R})$;
--   3. $H_k\to H$ in $C^\infty_{\mathrm{loc}}$;
--   4. for every action bound $A$ there is $K$ such that for $k\ge K$ every periodic orbit $R$ on $H_k^{-1}(1)$ with $\mathcal A(R)\le A$ has $\mu_{CZ}(R)\ge3$.
--
--   Then for all large $k$, $\bar P$, viewed as a periodic orbit $P_k$ of $X_{H_k}$ (same parametrization $\bar x$ and period $\bar T$), is the binding of a transverse disk open book on $H_k^{-1}(1)$.
--
--   A *transverse disk open book* on $S=G^{-1}(1)$ with binding $Q=(x,T)$ is a family of maps $\mathrm{page}_\theta:\mathbb{R}^2\to\mathbb{R}^4$, $\theta\in\mathbb{R}$, such that
--
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ is $C^\infty$ and $1$-periodic in $\theta$;
--   - each $\mathrm{page}_\theta$ restricts to a smooth embedding of the closed unit disk $\bar{\mathbb D}$ into $S$ (`IsSmoothDiskEmbedding`, injective differential up to the boundary);
--   - the boundary circle runs along $Q$: $\mathrm{page}_\theta(\cos2\pi t,\sin2\pi t)=x(Tt)$;
--   - $X_G$ is transverse to every page in the interior: $X_G(\mathrm{page}_\theta(u))\notin\operatorname{im}D\mathrm{page}_\theta(u)$ for $|u|<1$;
--   - $(\theta,u)\mapsto\mathrm{page}_\theta(u)$ maps $[0,1)\times\mathbb D$ bijectively onto $S\setminus x(\mathbb{R})$, with injective differential at every $(\theta,u)$, $|u|<1$.
--
--   This is an adapted open book decomposition (`AdaptedDiskOpenBook`) without the requirement that the pages be global surfaces of section and without the orientation condition on the pages.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. A Hamiltonian $H_k$ is *non-degenerate* when for every periodic orbit $R=(x,T)$ on $H_k^{-1}(1)$ (prime or not) and its linearized flow $Y$, the linearized return map on $\xi$, written in the global frame $(Z_1,Z_2)$ as the matrix $\varphi(1)$ of `linearizedXiPath`, does not have $1$ as an eigenvalue. The action of a periodic orbit $R=(x,T)$ is $\mathcal A(R)=\int_0^T\lambda_0(x(t))[\dot x(t)]\,dt$, with $\lambda_0=\tfrac12\sum(q_i\,dp_i-p_i\,dq_i)$ the Liouville form (`liouvilleForm`). The Conley–Zehnder index $\mu_{CZ}(R)$ is `czIndexOfPath` of the linearized flow on $\xi$ written in the global frame $(Z_1,Z_2)$ (`linearizedXiPath`), with its lower semicontinuous extension to degenerate orbits.
--
--   The hypotheses are exactly those of `bounds_global_section_of_approx_of_eventually_czIndex_ge_three`. This statement is the open book part of the conclusion of Hryniewicz's Section 3 for the contact forms $\lambda_k$, $k$ large; it does not assert that the pages are global surfaces of section.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Theorems 3.4, 3.10 and 3.11 (pp. 20-25) and p. 37; H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) 197-289, Theorems 2.2 and 2.5; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012) 1859-1931.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_transverse_disk_open_book_of_approx (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (P : PeriodicOrbit H) (hP : P.IsPrime) (hu : IsUnknotted H P)
    (hsl : HasSelfLinkingNumber H P (-1))
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hnd : (∀ k (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow (Hs k) R.x Y →
      ∀ v : Fin 2 → ℝ, (linearizedXiPath (Hs k) R Y 1).mulVec v = v → v = 0))
    (hjet : ∀ k, ∀ y ∈ P.image, Hs k y = H y ∧ fderiv ℝ (Hs k) y = fderiv ℝ H y)
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K))
    (hcz : (∀ A : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)),
      IsLinearizedFlow (Hs k) R.x Y → (∫ t in (0 : ℝ)..R.T, liouvilleForm (R.x t) (deriv R.x t)) ≤ A →
      3 ≤ czIndexOfPath (linearizedXiPath (Hs k) R Y))) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ Pk : PeriodicOrbit (Hs k), Pk.x = P.x → Pk.T = P.T →
      ∃ page : ℝ → Plane → R4,
      ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface (Hs k)) ∧
      (∀ θ t, page θ (circlePoint t) = Pk.x (Pk.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField (Hs k) (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface (Hs k), y ∉ Pk.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))) := by sorry
