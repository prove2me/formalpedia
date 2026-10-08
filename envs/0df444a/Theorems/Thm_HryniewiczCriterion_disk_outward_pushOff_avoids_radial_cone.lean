-- Prove2me | Theorems.Thm_HryniewiczCriterion_disk_outward_pushOff_avoids_radial_cone
-- name    : HryniewiczCriterion.disk_outward_pushOff_avoids_radial_cone
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T02:29:20.592156+00:00
-- url     : https://prove2.me/theorems/a93b8153-69f1-47b5-8719-8a335a952eca
-- title:
--   The outward push-off of the boundary of an embedded disk misses the radial cone over the disk
-- statement:
--   Let $e:\mathbb{R}^2\to\mathbb{R}^4$ be smooth, injective with injective differential on the closed unit disk $D$, with $e\ne0$ on $D$, $e(v)\notin\operatorname{range}de(v)$ on $D$ (radial transversality), and radially injective: $\mu e(v)=e(v')$ with $v,v'\in D$, $\mu>0$ forces $\mu=1$. Let $u,a:\mathbb{R}\to\mathbb{R}^2$ be continuous and $1$-periodic, with $|u|=1$ and $\langle u,a\rangle>0$ ($a$ points out of the disk). Then for all small $\varepsilon>0$, the point $e(u(s))+\varepsilon\,de(u(s))\,a(s)$ never lies on the cone $\{\mu e(v):v\in D,\ \mu\ge0\}$.
--
--   Proof: by contradiction with a convergent subsequence in $[0,1]\times D$. The limit forces $\mu\to1$ and $v\to u(s_0)$. The map $G(v,\mu)=\mu e(v)$ has injective differential at $(u(s_0),1)$, so it has a smooth local left inverse $L$. The function $f=|\pi_1L|^2$ is strictly differentiable, with $f'(de\,a)=2\langle u,a\rangle>0$. Hence $f$ at the push-off exceeds $f(e(u))=1\ge|v|^2$.
-- source:
--   Elementary (inverse function theorem and compactness); used for the Seifert framing of the binding in U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 1.7.

import Definitions.Def_HryniewiczCriterion_GlobalSection

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.disk_outward_pushOff_avoids_radial_cone (e : Plane → R4) (hE : ContDiff ℝ ∞ e)
    (hinjD : Set.InjOn e closedUnitDisk)
    (hinj : ∀ v ∈ closedUnitDisk, Function.Injective (fderiv ℝ e v))
    (htr : ∀ v ∈ closedUnitDisk, e v ∉ Set.range (fderiv ℝ e v))
    (h0 : ∀ v ∈ closedUnitDisk, e v ≠ 0)
    (hrad : ∀ v ∈ closedUnitDisk, ∀ v' ∈ closedUnitDisk, ∀ μ : ℝ, 0 < μ → μ • e v = e v' → μ = 1)
    (u a : ℝ → Plane) (hu : Continuous u) (ha : Continuous a)
    (huper : ∀ s, u (s + 1) = u s) (haper : ∀ s, a (s + 1) = a s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hua : ∀ s, 0 < u s 0 * a s 0 + u s 1 * a s 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s, ∀ v ∈ closedUnitDisk, ∀ μ : ℝ, 0 ≤ μ →
      e (u s) + ε • fderiv ℝ e (u s) (a s) ≠ μ • e v := by sorry
