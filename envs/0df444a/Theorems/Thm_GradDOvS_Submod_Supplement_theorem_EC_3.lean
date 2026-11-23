-- Prove2me | Theorems.Thm_GradDOvS_Submod_Supplement_theorem_EC_3
-- name    : GradDOvS.Submod.Supplement.theorem_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:21:25.468311+00:00
-- url     : https://prove2.me/theorems/281ebca9-4465-49ca-aef1-bc93858bd62f
-- title:
--   Theorem EC.3, p. ec16 (PDF 54) — an L♮-convex f has indifference zone c iff its convex extension satisfies the weak sharp minimum condition with κ = 1/c
-- statement:
--   Let $d \ge 1$, $N \ge 2$, let $f : \mathcal X = [N]^d \to \mathbb R$ be L♮-convex, let $\tilde f$ be its convex extension (7) on $[1,N]^d$, and let $c > 0$. Then the following are equivalent:
--
--   1. $f \in \mathcal{MC}_c$: $f$ has a minimizer $x^* \in \mathcal X$ with
--   $$f(x) - f(x^*) \ge c \qquad \text{for all } x \in \mathcal X \setminus \{x^*\};$$
--   2. $\tilde f$ satisfies the weak sharp minimum condition on $[1,N]^d$ with $\kappa = c^{-1}$: $\tilde f$ has a unique minimizer $\tilde x$ on $[1,N]^d$ and
--   $$\|x - \tilde x\|_\infty \le c^{-1}\,\big(\tilde f(x) - \tilde f(\tilde x)\big) \qquad \text{for all } x \in [1,N]^d .$$
--
--   The equivalence turns the discrete indifference-zone assumption into a growth condition of a convex function, which is what the accelerated PCS-IZ algorithm of EC.3.3 uses to shrink its search box.
--
--   **Formalization Note** $\tilde f$ is the canonical-choice extension of the definition file; by Theorem 3 it agrees with every admissible choice in (7). The $\ell_\infty$ norm is Lean's norm on `Fin d → ℝ`.
--
--   Differences from the source:
--   - encoding: "$f \in \mathcal{MC}_c$" for a given L♮-convex $f$ → $f$ has a minimizer $x^* \in [N]^d$ with $f(x^*) + c \le f(x)$ for all other $x \in [N]^d$; reason: membership in $\mathcal{MC}_c$ is L♮-convexity (a hypothesis) plus the indifference zone of p. 10, whose uniqueness of the minimizer follows from $c > 0$
--   - encoding: $f : \mathcal X \to \mathbb R$ → $f : \mathbb Z^d \to \mathbb R$ with only its values on $[N]^d$ used, and the hypotheses $d \ge 1$, $N \ge 2$ of Assumption 3; reason: Lean convention for a function on a subset; the hypotheses are the standing assumptions
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. ec16 (PDF 54), Theorem EC.3, with Definition EC.1 (p. ec16) and (7) (p. 22)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Supplement_ConvexExt

namespace GradDOvS.Submod.Supplement

/-- Theorem EC.3, p. ec16 (PDF 54): for an L♮-convex `f` on `X = [N]^d` with convex extension `f̃`
on `[1, N]^d` and a constant `c > 0`, `f` has indifference zone `c` (so `f ∈ MC_c`) if and only if
`f̃` satisfies the weak sharp minimum condition on `[1, N]^d` with `κ = c⁻¹` (in the `ℓ∞` norm). -/
theorem theorem_EC_3 (d N : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N) (f : (Fin d → ℤ) → ℝ)
    (hf : LNatConvexOn d N f) (c : ℝ) (hc : 0 < c) :
    HasIndifferenceZone d N f c ↔ IsWSM (realBox d N) (convexExt N f) c⁻¹ := by sorry

end GradDOvS.Submod.Supplement
