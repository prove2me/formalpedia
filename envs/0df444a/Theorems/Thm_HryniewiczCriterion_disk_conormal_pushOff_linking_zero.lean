-- Prove2me | Theorems.Thm_HryniewiczCriterion_disk_conormal_pushOff_linking_zero
-- name    : HryniewiczCriterion.disk_conormal_pushOff_linking_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:40:30.277689+00:00
-- url     : https://prove2.me/theorems/1622df8a-b34c-4267-9d2c-df08802e3c47
-- title:
--   The push-off of the boundary of an embedded disk along its $\xi$-projected conormal has linking number $0$
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped, $P=(x,T)$ a prime periodic orbit, and $e$ a smooth embedding of the closed unit disk into $S$ with $e(S^1)=x(\mathbb{R})$, and $u(s)$ a smooth $1$-periodic lift with $e(u(s))=x(Ts)$. Push $P$ off along the $\xi$-projection of the outward conormal $n(s)=de(u(s))\,u(s)$,
--   $$\gamma_\varepsilon(s)=\frac{x(Ts)+\varepsilon\,\pi_\xi n(s)}{|x(Ts)+\varepsilon\,\pi_\xi n(s)|},\qquad \pi_\xi n=n-\frac{\lambda_0(n)}{\lambda_0(X_H)}X_H .$$
--   Then for all small $\varepsilon>0$ the loops $s\mapsto x(Ts)/|x(Ts)|$ and $\gamma_\varepsilon$ in $S^3$ have linking number $0$, in the sense of `IsLinkingNumber` (Gauss integral after stereographic projection).
--
--   Proof idea: $\pi_\xi n$ and $n$ differ by a multiple of $X_H$, which is tangent to $P$, so the two push-offs are homotopic in the complement of $P$. The push-off along $n$ is close to $e((1+\varepsilon)u(s))$, which bounds the disk $\rho\mapsto e(\rho\,u)$, $\rho\le 1+\varepsilon$, missing $P$ after radial projection. So it is null-homotopic in $S^3\setminus P$, and the Gauss integral vanishes. This is the statement that the Seifert framing of a knot bounding a disk is $0$.
-- source:
--   Seifert framing of the boundary of an embedded disk (Rolfsen, Knots and Links, 1976, Ch. 5D); the step $\mathrm{link}(P,P')=0$ for the disk push-off in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, Proposition 2.1 (cited for necessity in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, outline after Theorem 1.8).

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.disk_conormal_pushOff_linking_zero (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsLinkingNumber (orbitLoop P)
        (fun s => radialNormalize (P.x (P.T * s) + ε • (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))))) 0 := by sorry
