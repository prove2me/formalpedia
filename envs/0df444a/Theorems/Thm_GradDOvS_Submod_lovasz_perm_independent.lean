-- Prove2me | Theorems.Thm_GradDOvS_Submod_lovasz_perm_independent
-- name    : GradDOvS.Submod.lovasz_perm_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:51.290853+00:00
-- url     : https://prove2.me/theorems/394f0f30-8bd7-42c6-8349-e006d3766a44
-- title:
--   p. 17, after (2) — the Lovász extension does not depend on the consistent permutation
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$ be any set function and $x \in [0,1]^d$. If $\alpha$ and $\beta$ are two consistent permutations of $x$, i.e. $x_{\alpha(1)} \ge \dots \ge x_{\alpha(d)}$ and $x_{\beta(1)} \ge \dots \ge x_{\beta(d)}$, then formula (2) gives the same value with either:
--   $$f(S^{x,0}_\alpha) + \sum_{i=1}^d \big[f(S^{x,i}_\alpha) - f(S^{x,i-1}_\alpha)\big] x_{\alpha(i)} = f(S^{x,0}_\beta) + \sum_{i=1}^d \big[f(S^{x,i}_\beta) - f(S^{x,i-1}_\beta)\big] x_{\beta(i)},$$
--   where $S^{x,i}_\alpha = \{\alpha(1),\dots,\alpha(i)\}$.
--
--   This makes the Lovász extension $\tilde f$ a well-defined function of $x$, independent of how ties among the coordinates of $x$ are ordered.
--
--   **Formalization Note** No submodularity is needed, so the statement is made for every $f$ (stronger than the setting of the page).
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 17, sentence after eq. (2)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- p. 17, after (2): the value of the Lovász extension (2) at `x ∈ [0,1]^d` does not depend on
the consistent permutation of `x` used to evaluate it. -/
theorem lovasz_perm_independent {d : ℕ} (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (hx : x ∈ box d)
    (α β : Equiv.Perm (Fin d)) (hα : IsConsistentPerm x α) (hβ : IsConsistentPerm x β) :
    lovaszWith f x α = lovaszWith f x β := by sorry

end GradDOvS.Submod
