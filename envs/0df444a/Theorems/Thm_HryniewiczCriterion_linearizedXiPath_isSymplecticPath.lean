-- Prove2me | Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath
-- name    : HryniewiczCriterion.linearizedXiPath_isSymplecticPath
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:11:50.159709+00:00
-- url     : https://prove2.me/theorems/25edf73f-d112-48c6-8bc5-b3b08f956d95
-- title:
--   The linearized flow on $\xi$ in the quaternionic frame is a path in $Sp(1)$
-- statement:
--   Let $H:\mathbb{R}^4\to\mathbb{R}$ be smooth and let $S=H^{-1}(1)$ be strictly star-shaped. Let $P=(x,T)$ be a periodic orbit of $X_H$ on $S$ and let $Y$ solve the variational equation
--   $$Y(0)=\mathrm{id},\qquad \dot Y(t)=DX_H(x(t))\,Y(t).$$
--   Let $\varphi(\tau)$, $\tau\in[0,1]$, be the matrix of the linearized flow on $\xi=\ker\lambda_0\cap TS$ in the global frame $Z_1,Z_2$: column $j$ holds the $(Z_1,Z_2)$-coordinates of $\pi_{x(T\tau)}\,Y(T\tau)\,Z_j(x(0))$, where $\pi_x$ projects $T_xS$ onto $\ker\lambda_0(x)$ along $X_H(x)$.
--
--   Then $\varphi$ is a smooth path in $Sp(1)=SL(2,\mathbb{R})$ that starts at the identity:
--   $$\varphi\in C^\infty([0,1]),\qquad \det\varphi(\tau)=1\ \ (0\le\tau\le1),\qquad \varphi(0)=I.$$
--
--   This is the standing fact behind Hryniewicz's definition of $\mu_{CZ}(P)$ (Section 2.1.1): the index is defined for paths in $Sp(1)$ starting at $I$. The determinant identity holds because $Y(t)$ preserves $\omega_0$ and maps $T_{x(0)}S$ to $T_{x(t)}S$, the projection $\pi_x$ changes vectors of $TS$ only by multiples of $X_H$ (which is $\omega_0$-orthogonal to $TS$), and $\omega_0(Z_1,Z_2)=1$.
--
--   **Formalization Note** The path is `linearizedXiPath H P Y`, smoothness is `ContDiffOn ℝ ∞` of its entries on $[0,1]$, and these are exactly the hypotheses of `HryniewiczCriterion.winding_endpoint_profile`.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Section 2.1.1, pp. 5-6 (paths in Sp(1) starting at I) and Section 3, p. 12 (global frame of xi on star-shaped levels)

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open scoped ContDiff

namespace HryniewiczCriterion

/-- Hryniewicz, arXiv:1105.2077, §2.1 and §3 (pp. 5–6, 12): on a strictly star-shaped
level `S = H⁻¹(1)`, the linearized flow on `ξ = ker λ₀|S` along a periodic orbit,
written in the global symplectic frame `Z₁, Z₂`, is a smooth path in `Sp(1) = SL(2, ℝ)`
starting at the identity. -/
theorem linearizedXiPath_isSymplecticPath (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath H P Y t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath H P Y t).det = 1) ∧
      linearizedXiPath H P Y 0 = 1 := by sorry

end HryniewiczCriterion
