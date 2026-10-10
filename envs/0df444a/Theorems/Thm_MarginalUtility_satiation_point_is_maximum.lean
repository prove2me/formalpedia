-- Prove2me | Theorems.Thm_MarginalUtility_satiation_point_is_maximum
-- name    : MarginalUtility.satiation_point_is_maximum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:24.795761+00:00
-- url     : https://prove2.me/theorems/cfaa60c6-7b12-427e-9124-1af2c18b2aef
-- title:
--   Zero marginal utility: total utility is maximal, and marginal utility is negative beyond
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $D\subseteq\mathbb R$ be an open interval, let $U$ have diminishing marginal utility on $D$, and suppose the marginal utility vanishes at some $x_0\in D$. Then total utility is at its maximum at $x_0$, i.e. $U(x)\le U(x_0)$ for all $x\in D$, and beyond that point marginal utility is negative: $\partial U/\partial g\,(x)<0$ for every $x\in D$ with $x>x_0$.
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem satiation_point_is_maximum (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D)
    (x₀ : ℝ) (hx₀ : x₀ ∈ D) (hzero : marginalUtility U x₀ = 0) :
    IsMaxOn U D x₀ ∧ ∀ x ∈ D, x₀ < x → marginalUtility U x < 0 := by sorry

end MarginalUtility
