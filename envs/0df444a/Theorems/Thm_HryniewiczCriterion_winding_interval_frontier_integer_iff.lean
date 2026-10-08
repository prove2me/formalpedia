-- Prove2me | Theorems.Thm_HryniewiczCriterion_winding_interval_frontier_integer_iff
-- name    : HryniewiczCriterion.winding_interval_frontier_integer_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T18:52:39.865301+00:00
-- url     : https://prove2.me/theorems/3c5f7b4b-e64c-41f3-95bc-e04a1643a8c7
-- title:
--   Lemma 2.1: an endpoint of the winding interval is an integer iff $\varphi(1)$ has eigenvalue $1$
-- statement:
--   Let $\varphi:[0,1]\to Sp(1)$ be a smooth path of $2\times2$ real matrices with $\det\varphi(t)=1$ and $\varphi(0)=I$, and let $I(\varphi)=[a,b]$ be its winding interval (total rotations of the vectors $e^{is}$, in turns). Then
--   $$\partial I(\varphi)\cap\mathbb{Z}\neq\emptyset\iff\det\big(\varphi(1)-I\big)=0,$$
--   that is, an endpoint $a$ or $b$ of the winding interval is an integer exactly when $1$ is an eigenvalue of $\varphi(1)$, i.e. $\varphi\notin\Sigma^*(1)$.
--
--   This identifies degenerate paths with paths whose winding interval has an integer endpoint. It is the basis of the formula for the Conley–Zehnder index by winding intervals and of its lower semicontinuous extension to degenerate paths.
--
--   **Formalization Note** Smoothness is asked for the entries $t\mapsto\varphi(t)_{ij}$ on $[0,1]$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Section 2.1.1, Lemma 2.1, p. 6

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open scoped ContDiff

namespace HryniewiczCriterion

/-- Hryniewicz, Lemma 2.1: for a smooth path `φ : [0, 1] → Sp(1)` with `φ(0) = I`,
an endpoint of the winding interval `I(φ)` is an integer iff `φ(1)` has eigenvalue `1`. -/
theorem winding_interval_frontier_integer_iff (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    (∃ k : ℤ, sInf (windingInterval φ) = k ∨ sSup (windingInterval φ) = k) ↔
      (φ 1 - 1).det = 0 := by sorry

end HryniewiczCriterion
