-- Prove2me | Theorems.Thm_KelsoCrawford_Returns_two_workers_gs_iff_subadditive
-- name    : KelsoCrawford.Returns.two_workers_gs_iff_subadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:10.895472+00:00
-- url     : https://prove2.me/theorems/3b1b1635-b770-45e4-9e4f-4b5000a4cb96
-- title:
--   Section 6, p. 1500 — with two heterogeneous workers, (GS) is equivalent to subadditivity
-- statement:
--   Let $W = \{a, b\}$ consist of exactly two workers, and let $y : 2^W \to \mathbb{R}$ be an arbitrary production technology (workers need not be alike in production) with $y(\emptyset) = 0$. Then $y$ satisfies the gross-substitutes condition (GS) for real salary vectors if and only if $y$ is subadditive, $y(C \cup D) \le y(C) + y(D)$ for disjoint $C, D$; with two workers this is
--   $$v_1 + v_2 \ge v_{12}, \qquad v_1 = y(\{a\}),\ v_2 = y(\{b\}),\ v_{12} = y(\{a, b\}).$$
--
--   The paper contrasts this with three or more workers, where subadditivity no longer implies (GS).
--
--   **Formalization Note** The normalization $y(\emptyset) = 0$ is the paper's ("recall that $y^j(\emptyset) \equiv 0$"). Subadditivity is stated in the paper's general form over all disjoint pairs of sets; with two workers and $y(\emptyset) = 0$ it reduces to $v_1 + v_2 \ge v_{12}$. Salaries range over all of $\mathbb{R}^W$.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1500, Section 6, the two-worker claim and eq. (20)

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology

namespace KelsoCrawford.Returns

theorem two_workers_gs_iff_subadditive {W : Type} [Fintype W] [DecidableEq W]
    (hW : Fintype.card W = 2) (y : Finset W → ℝ) (hy0 : y ∅ = 0) :
    KelsoCrawford.Process.GrossSubstitutesOn y Set.univ ↔ Subadditive y := by sorry

end KelsoCrawford.Returns
