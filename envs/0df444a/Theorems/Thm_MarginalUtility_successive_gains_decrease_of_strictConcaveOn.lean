-- Prove2me | Theorems.Thm_MarginalUtility_successive_gains_decrease_of_strictConcaveOn
-- name    : MarginalUtility.successive_gains_decrease_of_strictConcaveOn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:59.528987+00:00
-- url     : https://prove2.me/theorems/b298012f-3f43-47a6-903a-5529d68607ad
-- title:
--   Concave utility: each equal gain adds less than the previous one
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $U$ be strictly concave on a convex set $D\subseteq\mathbb R$ (a concave relation between objective gains and subjective value). If $h>0$ and both $x$ and $x+2h$ lie in $D$, then the second gain of size $h$ produces a strictly smaller increase in subjective value than the first:
--   $$U(x+2h)-U(x+h)<U(x+h)-U(x).$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem successive_gains_decrease_of_strictConcaveOn (U : ℝ → ℝ) (D : Set ℝ)
    (hU : StrictConcaveOn ℝ D U) (x h : ℝ) (hh : 0 < h)
    (hx : x ∈ D) (hx2 : x + 2 * h ∈ D) :
    utilityChange U (x + h) (x + 2 * h) < utilityChange U x (x + h) := by sorry

end MarginalUtility
