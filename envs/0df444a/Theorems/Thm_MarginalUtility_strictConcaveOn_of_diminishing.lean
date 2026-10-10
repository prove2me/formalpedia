-- Prove2me | Theorems.Thm_MarginalUtility_strictConcaveOn_of_diminishing
-- name    : MarginalUtility.strictConcaveOn_of_diminishing
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:20.214203+00:00
-- url     : https://prove2.me/theorems/e0a0b52b-7450-4981-bf24-25250f056be5
-- title:
--   Diminishing marginal utility gives a strictly concave utility function
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $D\subseteq\mathbb R$ be an open interval and let $U$ have diminishing marginal utility on $D$. Then $U$ is strictly concave on $D$: for all $x\neq y$ in $D$ and $0<t<1$,
--   $$U\big(tx+(1-t)y\big)>tU(x)+(1-t)U(y).$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem strictConcaveOn_of_diminishing (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictConcaveOn ℝ D U := by sorry

end MarginalUtility
