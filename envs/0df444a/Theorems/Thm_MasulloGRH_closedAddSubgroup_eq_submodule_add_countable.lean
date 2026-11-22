-- Prove2me | Theorems.Thm_MasulloGRH_closedAddSubgroup_eq_submodule_add_countable
-- name    : MasulloGRH.closedAddSubgroup_eq_submodule_add_countable
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:22:35.085209+00:00
-- url     : https://prove2.me/theorems/16293bb8-ed59-4480-aeb0-b213cd0fe264
-- title:
--   A closed subgroup of a finite-dimensional real vector space is a subspace plus a countable set
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space and let $H\le E$ be a closed additive subgroup. Then $H$ is the sum of a linear subspace contained in $H$ and a countable subset of $H$: there are a subspace $V\subseteq H$ and a countable set $D\subseteq H$ such that
--   $$
--   H \;=\; V + D \;=\; \{\,v+\delta:\ v\in V,\ \delta\in D\,\}.
--   $$
--   In fact one can take for $V$ the largest subspace contained in $H$, namely $V=\{v:\ \mathbb R v\subseteq H\}$, and $D=H\cap W$ for any linear complement $W$ of $V$; then $H\cap W$ is discrete.
--
--   This is the first step of the classical structure theorem for closed subgroups of $\mathbb R^N$ ($H\cong\mathbb R^a\times\mathbb Z^b$). In the Schwartz–Bruhat theory of Masullo's Appendix D it is used to lift one-parameter subgroups through correspondences between elementary groups $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$. Combined with the Baire category theorem, it shows that if the image of $H$ under a linear map is all of $\mathbb R^k$, then so is the image of $V$.
-- source:
--   N. Bourbaki, General Topology, Ch. VII §1.2, Theorem 2 (closed subgroups of $\mathbb R^n$); used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix D, §D.1.3 (elementary groups)

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Ring.Star

set_option autoImplicit false

namespace MasulloGRH

theorem closedAddSubgroup_eq_submodule_add_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ V : Submodule ℝ E, (V : Set E) ⊆ H ∧ ∃ D : Set E, D.Countable ∧ D ⊆ H ∧
      ∀ h ∈ H, ∃ v ∈ V, ∃ δ ∈ D, h = v + δ := by
  sorry

end MasulloGRH
