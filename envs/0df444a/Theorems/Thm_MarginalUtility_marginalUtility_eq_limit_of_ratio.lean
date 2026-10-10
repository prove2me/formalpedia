-- Prove2me | Theorems.Thm_MarginalUtility_marginalUtility_eq_limit_of_ratio
-- name    : MarginalUtility.marginalUtility_eq_limit_of_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:47.597297+00:00
-- url     : https://prove2.me/theorems/a8999763-c6aa-44cb-846e-ed22455e1d01
-- title:
--   Marginal utility as the limit of $\Delta U/\Delta g$
-- statement:
--   Throughout, a utility function of one quantified variable is a map $U:\mathbb R\to\mathbb R$ (all other variables held fixed, *ceteris paribus*); $\Delta U(s_1\to s_2)=U(s_2)-U(s_1)$ is the change in utility from state $s_1$ to state $s_2$; the marginal utility at $g$ is $\partial U/\partial g=U'(g)$; and $U$ has *diminishing marginal utility* on a set $D\subseteq\mathbb R$ when $U$ and $U'$ are differentiable on $D$ and $\partial^2U/\partial g^2<0$ at every point of $D$. An *open interval* $D$ below means an open convex subset of $\mathbb R$ (possibly empty, possibly unbounded).
--
--   Let $U:\mathbb R\to\mathbb R$ be differentiable at $g$. Then the ratio of the change in utility to the size of the change in $g$ converges to the marginal utility:
--   $$\lim_{\Delta g\to 0,\ \Delta g\neq 0}\frac{U(g+\Delta g)-U(g)}{\Delta g}=\frac{\partial U}{\partial g}(g).$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Filter Topology Set

namespace MarginalUtility

theorem marginalUtility_eq_limit_of_ratio (U : ℝ → ℝ) (g : ℝ)
    (hU : DifferentiableAt ℝ U g) :
    Tendsto (fun Δg : ℝ => utilityChange U g (g + Δg) / Δg) (𝓝[≠] 0)
      (𝓝 (marginalUtility U g)) := by sorry

end MarginalUtility
