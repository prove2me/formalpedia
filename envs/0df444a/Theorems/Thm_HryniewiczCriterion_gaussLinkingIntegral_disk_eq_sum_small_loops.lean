-- Prove2me | Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_disk_eq_sum_small_loops
-- name    : HryniewiczCriterion.gaussLinkingIntegral_disk_eq_sum_small_loops
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:10:42.791536+00:00
-- url     : https://prove2.me/theorems/44322f7f-1db1-4853-98d9-94169b178a3f
-- title:
--   Residue formula for the Gauss linking form: the boundary of a disk links a knot as often as small loops around the crossing points
-- statement:
--   Let $E:\mathbb{R}^2\to\mathbb{R}^4$ be $C^2$ on an open neighbourhood of the closed unit disk $\overline{\mathbb D}$ with $|E|=1$ on $\overline{\mathbb D}$, and let $\gamma:\mathbb{R}\to S^3$ be a $C^2$ loop of period $1$. Suppose $E(v)\in\gamma(\mathbb{R})$ only for $v$ in a finite set $Z$ of interior points of the disk, and let $N\in S^3$ miss $\gamma$ and $E(\overline{\mathbb D})$. Then for all small $\rho>0$
--   $$\mathrm{Gauss}_N\big(E\circ c_{0,1},\gamma\big)=\sum_{z\in Z}\mathrm{Gauss}_N\big(E\circ c_{z,\rho},\gamma\big),\qquad c_{z,\rho}(s)=z+\rho(\cos2\pi s,\sin2\pi s),$$
--   where $\mathrm{Gauss}_N$ is `gaussLinkingIntegral` (stereographic projection from $N$). No transversality or injectivity is needed.
--
--   This is the residue theorem for the closed $1$-form $\alpha=E^*\omega_\gamma$ on $\overline{\mathbb D}\setminus Z$, where $\omega_\gamma$ is the Biot–Savart (linking) form of $\gamma$: $\mathrm{Gauss}_N(E\circ c,\gamma)=\oint_c\alpha$.
--
--   Suggested proof (homotopy only, no Stokes). Gauss integrals are invariant under $C^2$ homotopies of the first loop in $E(\overline{\mathbb D}\setminus Z)$ (`gaussIntegral_eq_of_homotopy`). Choose a centre $c$ so that the points of $Z$ lie on distinct rays from $c$ and work with graph loops $s\mapsto E(c+h(s)(\partial(s)-c))$; move $h$ from $1$ to $0$ past one point at a time with flat bump functions. Two graph loops that differ only on a short parameter interval differ in Gauss integral by the integral over a closed loop around one point of $Z$ (fixed-endpoint arc variations leave the partial Gauss integral unchanged), and that loop is homotopic to $c_{z,\rho}$ in $\overline{\mathbb D}\setminus Z$. The constant loop at $h\equiv0$ has Gauss integral $0$.
-- source:
--   Standard (homological invariance of the linking integral; residue theorem for closed 1-forms on a punctured disk), e.g. D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D (linking number = algebraic intersection number with a Seifert surface)

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.gaussLinkingIntegral_disk_eq_sum_small_loops (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1)
    (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk)
    (hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t)
    (N : R4) (hN : euclidNorm N = 1) (hNγ : ∀ t, γ t ≠ N)
    (hNE : ∀ v ∈ closedUnitDisk, E v ≠ N) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      gaussLinkingIntegral N (fun s => E (circlePoint s)) γ =
        ∑ z ∈ Z, gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ := by sorry
