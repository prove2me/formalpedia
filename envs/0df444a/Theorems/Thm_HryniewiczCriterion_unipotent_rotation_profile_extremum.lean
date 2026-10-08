-- Prove2me | Theorems.Thm_HryniewiczCriterion_unipotent_rotation_profile_extremum
-- name    : HryniewiczCriterion.unipotent_rotation_profile_extremum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:23:46.486976+00:00
-- url     : https://prove2.me/theorems/41eee873-a4d2-407a-8fba-548472e28338
-- title:
--   A continuous angular displacement of a unipotent plane matrix has an integer extremum
-- statement:
--   Let $A$ be a real $2\times2$ matrix satisfying $\det A=1$ and $\det(A-I)=0$. Let $\Delta:\mathbb R\to\mathbb R$ be continuous and suppose that for every $s$ there is $r>0$ such that
--   $$A(\cos s,\sin s)=r\,(\cos(s+2\pi\Delta(s)),\sin(s+2\pi\Delta(s))).$$
--   Then some integer is an attained global minimum or an attained global maximum:
--   $$\exists k\in\mathbb Z,\quad
--   \bigl(k\in\Delta(\mathbb R)\ \text{and}\ \forall s,\ k\le\Delta(s)\bigr)
--   \quad\text{or}\quad
--   \bigl(k\in\Delta(\mathbb R)\ \text{and}\ \forall s,\ \Delta(s)\le k\bigr).$$
--   This is the identity-or-shear part of the reverse implication of Hryniewicz's Lemma 2.1, stated solely in terms of the endpoint matrix and a continuous angular displacement, so it can be reused independently of a chosen path.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, https://arxiv.org/abs/1105.2077, Section 2.1.1, pp. 5–6, angular description preceding Lemma 2.1 and its proof.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped ContDiff

theorem HryniewiczCriterion.unipotent_rotation_profile_extremum
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1)
    (hdeg : (A - 1).det = 0) (Δ : ℝ → ℝ) (hΔ : Continuous Δ)
    (hpolar : ∀ s : ℝ, ∃ r : ℝ, 0 < r ∧
      A.mulVec (rotationVector s) = r • rotationVector (s + 2 * Real.pi * Δ s)) :
    ∃ k : ℤ, IsLeast (Set.range Δ) (k : ℝ) ∨
      IsGreatest (Set.range Δ) (k : ℝ) := by sorry
