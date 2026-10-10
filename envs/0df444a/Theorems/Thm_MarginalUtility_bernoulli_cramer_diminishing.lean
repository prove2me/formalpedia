-- Prove2me | Theorems.Thm_MarginalUtility_bernoulli_cramer_diminishing
-- name    : MarginalUtility.bernoulli_cramer_diminishing
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:53.837972+00:00
-- url     : https://prove2.me/theorems/d653affa-0086-4220-b488-8bce4e37e2df
-- title:
--   Bernoulli's $\log$ and Cramer's $\sqrt{\cdot}$ have diminishing marginal utility
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Both measures of the desirability of a sum of money $x>0$ proposed in the 18th century have diminishing marginal utility on $(0,\infty)$: Bernoulli's natural logarithm $U(x)=\log x$ and Cramer's square root $U(x)=\sqrt x$ are twice differentiable on $(0,\infty)$ with $U''(x)<0$ for every $x>0$.
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem bernoulli_cramer_diminishing :
    HasDiminishingMarginalUtility Real.log (Ioi 0) ∧
      HasDiminishingMarginalUtility Real.sqrt (Ioi 0) := by sorry

end MarginalUtility
