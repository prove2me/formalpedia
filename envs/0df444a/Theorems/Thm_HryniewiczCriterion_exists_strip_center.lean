-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_strip_center
-- name    : HryniewiczCriterion.exists_strip_center
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:55:13.061656+00:00
-- url     : https://prove2.me/theorems/00f84187-006e-454f-b3c8-898463dbf427
-- title:
--   Strip coordinates for a punctured disk: a centre from which finitely many interior points lie on distinct rays
-- statement:
--   Let $Z$ be a finite set of points of the open unit disk $\mathbb D\subset\mathbb R^2$ and write $\partial(s)=(\cos2\pi s,\sin2\pi s)$ (`circlePoint`). Then there is a centre $c\in\mathbb D$ such that, in the "strip coordinates" $\Psi(\mu,s)=c+\mu(\partial(s)-c)$, every $z\in Z$ has unique coordinates: there are $\lambda_z\in(0,1)$ and $s_z\in\mathbb R$ with $z=\Psi(\lambda_z,s_z)$, and $\Psi(\mu,s)=z$ with $\mu\ge0$ forces $\mu=\lambda_z$ and $s\in s_z+\mathbb Z$. Moreover distinct points of $Z$ have $s_z\not\equiv s_w \pmod 1$, i.e. they lie on distinct rays from $c$.
--
--   Proof. Choose $c\in\mathbb D$ off the finitely many lines through two points of $Z$ and off $Z$ (a finite union of lines is Lebesgue-null and $\mathbb D$ has positive measure). For $z\in Z$ the ray from $c$ through $z$ leaves the disk at a unique point $\partial(s_z)$, at distance $t_z>|z-c|$ from $c$ (the positive root of $|c+td|^2=1$); put $\lambda_z=|z-c|/t_z$. If $\Psi(\mu,s)=z$ then $\mu>0$ (as $z\ne c$) and $\partial(s)-c$ is a positive multiple of $z-c$, so $\partial(s)=\partial(s_z)$ and $\mu=\lambda_z$. If $s_z\equiv s_w$ then $c,z,w$ are collinear, which was excluded.
-- source:
--   Elementary plane geometry (used for the residue formula for the Gauss linking integral)

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_strip_center (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk) :
    ∃ c : Plane, c ∈ openUnitDisk ∧ ∃ lam sp : Plane → ℝ, ∀ z ∈ Z,
      0 < lam z ∧ lam z < 1 ∧ z = c + lam z • (circlePoint (sp z) - c) ∧
      (∀ μ s : ℝ, 0 ≤ μ → c + μ • (circlePoint s - c) = z → μ = lam z ∧ ∃ n : ℤ, s = sp z + n) ∧
      (∀ w ∈ Z, w ≠ z → ∀ n : ℤ, sp w ≠ sp z + n) := by sorry
