-- Prove2me | Theorems.Thm_MarginalUtility_utility_monotone_of_marginal_sign
-- name    : MarginalUtility.utility_monotone_of_marginal_sign
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:18.030986+00:00
-- url     : https://prove2.me/theorems/3d8cddcf-f4be-4367-a8a5-2dcf1b29eb61
-- title:
--   Positive marginal utility raises utility; negative marginal utility lowers it
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $D\subseteq\mathbb R$ be an open interval and let $U$ be differentiable on $D$. (a) If the marginal utility is positive at every point of $D$, then every increase of consumption within $D$ strictly increases utility: $U$ is strictly increasing on $D$. (b) If the marginal utility is negative at every point of $D$, then every increase of consumption within $D$ strictly decreases utility: $U$ is strictly decreasing on $D$.
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem utility_monotone_of_marginal_sign (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : DifferentiableOn ℝ U D) :
    ((∀ g ∈ D, 0 < marginalUtility U g) → StrictMonoOn U D) ∧
      ((∀ g ∈ D, marginalUtility U g < 0) → StrictAntiOn U D) := by sorry

end MarginalUtility
