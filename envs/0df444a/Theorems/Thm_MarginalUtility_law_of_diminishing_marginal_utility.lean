-- Prove2me | Theorems.Thm_MarginalUtility_law_of_diminishing_marginal_utility
-- name    : MarginalUtility.law_of_diminishing_marginal_utility
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:52.452563+00:00
-- url     : https://prove2.me/theorems/462e30b5-77d8-494d-b23d-38acae186c67
-- title:
--   The law of diminishing marginal utility
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $D\subseteq\mathbb R$ be an open interval and let $U$ have diminishing marginal utility on $D$, i.e. $\partial^2U/\partial g^2<0$ on $D$. Then (i) as the amount consumed increases, marginal utility goes on decreasing: $U'$ is strictly decreasing on $D$; and (ii) each additional gain produces a smaller increase in utility than the previous gain of equal size: for every $h>0$ and $x$ with $x,\,x+2h\in D$,
--   $$U(x+2h)-U(x+h)<U(x+h)-U(x).$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem law_of_diminishing_marginal_utility (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictAntiOn (marginalUtility U) D ∧
      ∀ x h : ℝ, 0 < h → x ∈ D → x + 2 * h ∈ D →
        utilityChange U (x + h) (x + 2 * h) < utilityChange U x (x + h) := by sorry

end MarginalUtility
