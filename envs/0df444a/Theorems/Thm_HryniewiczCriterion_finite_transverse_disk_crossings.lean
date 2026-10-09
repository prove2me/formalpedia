-- Prove2me | Theorems.Thm_HryniewiczCriterion_finite_transverse_disk_crossings
-- name    : HryniewiczCriterion.finite_transverse_disk_crossings
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T19:10:35.469053+00:00
-- url     : https://prove2.me/theorems/50ff2e68-892e-4521-8232-fcfc2a574722
-- title:
--   A loop crossing a disk transversally crosses it at only finitely many points
-- statement:
--   Let $E:\mathbb{R}^2\to\mathbb{R}^4$ be $C^1$ on an open neighbourhood of the closed unit disk $\overline{\mathbb D}$ and let $\gamma:\mathbb{R}\to\mathbb{R}^4$ be a $C^1$ loop of period $1$. Suppose that at every crossing $E(v)=\gamma(t)$ with $v\in\overline{\mathbb D}$,
--   $$\det\big(\gamma(t),\gamma'(t),\partial_1E(v),\partial_2E(v)\big)\neq0$$
--   (rows of a $4\times4$ matrix). Then the set of crossing points $\{v\in\overline{\mathbb D}:\exists t,\ E(v)=\gamma(t)\}$ is finite.
--
--   Proof. At a crossing the three vectors $\gamma'(t),\partial_1E(v),\partial_2E(v)$ are linearly independent, so the map $(t,v)\mapsto\gamma(t)-E(v)$ from $\mathbb{R}^3$ to $\mathbb{R}^4$ has injective differential there and is injective near $(t,v)$ (inverse function theorem / local left inverse). Hence crossings are isolated in $[0,1]\times\overline{\mathbb D}$, a compact set, so there are finitely many pairs $(t,v)$ with $t\in[0,1]$, and by periodicity every crossing point $v$ arises from such a pair.
-- source:
--   Standard transversality and compactness argument, e.g. D. Rolfsen, Knots and Links, Publish or Perish 1976, Ch. 5D (linking number = algebraic intersection number with a Seifert surface)

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.finite_transverse_disk_crossings (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 1 E U)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 1 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]) ≠ 0) :
    {v : Plane | v ∈ closedUnitDisk ∧ ∃ t, E v = γ t}.Finite := by sorry
