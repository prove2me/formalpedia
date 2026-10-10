-- Prove2me | Theorems.Thm_MarginalUtility_marginalUtility_strictAntiOn
-- name    : MarginalUtility.marginalUtility_strictAntiOn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:50.78722+00:00
-- url     : https://prove2.me/theorems/e2339d75-b2b9-4427-8c1c-265789762b80
-- title:
--   Diminishing marginal utility: marginal utility goes on decreasing
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $D\subseteq\mathbb R$ be an open interval and let $U$ have diminishing marginal utility on $D$ ($\partial^2U/\partial g^2<0$ on $D$). Then, as the amount consumed increases within $D$, the marginal utility strictly decreases: for $g_1<g_2$ in $D$,
--   $$\frac{\partial U}{\partial g}(g_2)<\frac{\partial U}{\partial g}(g_1).$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem marginalUtility_strictAntiOn (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictAntiOn (marginalUtility U) D := by sorry

end MarginalUtility
