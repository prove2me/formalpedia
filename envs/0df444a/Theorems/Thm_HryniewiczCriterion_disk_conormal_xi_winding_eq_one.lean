-- Prove2me | Theorems.Thm_HryniewiczCriterion_disk_conormal_xi_winding_eq_one
-- name    : HryniewiczCriterion.disk_conormal_xi_winding_eq_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:40:37.976041+00:00
-- url     : https://prove2.me/theorems/d9fde2cb-e398-4c77-83c8-bfd22a98c173
-- title:
--   The $\xi$-projected outward conormal of a disk transverse to the flow winds once relative to the global frame
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $P=(x,T)$ a prime periodic orbit, and $e$ a smooth embedding of the closed unit disk into $S$ with $e(S^1)=x(\mathbb{R})$ and $X_H(e(u))\notin \operatorname{im} de(u)$ for $|u|<1$. Let $u(s)$ be a smooth $1$-periodic lift with $e(u(s))=x(Ts)$. Let $n(s)=de(u(s))\,u(s)$ be the outward conormal of the disk along its boundary, and let
--   $$\pi_\xi n=n-\frac{\lambda_0(n)}{\lambda_0(X_H)}\,X_H$$
--   be its projection to $\xi=\ker\lambda_0\cap TS$ along $X_H$. Then $\pi_\xi n(s)=r(s)\big(\cos\theta(s)\,Z_1+\sin\theta(s)\,Z_2\big)$ at $x(Ts)$, with smooth $r>0$ $1$-periodic and smooth $\theta$ satisfying
--   $$\theta(s+1)=\theta(s)+2\pi .$$
--   That is, the conormal winds exactly once, positively, relative to the global frame $(Z_1,Z_2)$ of $\xi$, where $\omega_0(Z_1,Z_2)=1$.
--
--   Proof idea: $\pi_\xi n$ is intrinsic to the disk, so we may reflect $e$ to make $d\lambda_0|_D>0$. Transversality makes the projection along $X_H$ an orientation-preserving isomorphism $TD\to\xi$ over the open disk. The frame $(\pi_\xi\partial_1 e,\pi_\xi\partial_2 e)$ extends over the disk, so it has winding $0$ relative to $(Z_1,Z_2)$, and the radial vector $\pi_\xi\partial_r e$ winds $+1$. At the boundary, $\ker(\pi_\xi|_{TD})=\mathbb{R}X_H=T\partial D$, so $\pi_\xi\partial_r e\ne0$ up to $|u|=1$. By Stokes, the boundary orientation matches the flow direction.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, Proposition 2.1 (cited for necessity in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, outline after Theorem 1.8); the frame argument of its proof.

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.disk_conormal_xi_winding_eq_one (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧ (∀ s, r (s + 1) = r s) ∧
      (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))) =
        r s • (Real.cos (θ s) • xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s))) := by sorry
