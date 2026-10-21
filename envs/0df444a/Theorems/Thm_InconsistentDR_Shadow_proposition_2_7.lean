-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_proposition_2_7
-- name    : InconsistentDR.Shadow.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:29.13162+00:00
-- url     : https://prove2.me/theorems/8bce6758-0963-4076-a67d-c90d481919d8
-- title:
--   Proposition 2.7, p. 9 — argmin(f + g) = zer ∂(f + g) = zer(∂f + ∂g) when zer(∂f + ∂g) ≠ ∅
-- statement:
--   Let $X$ be a real Hilbert space and let $f, g \in \Gamma_0(X)$ be proper, convex and lower semicontinuous, with values in $]-\infty,+\infty]$. Suppose that $\operatorname{zer}(\partial f + \partial g) = \{x \mid 0 \in \partial f(x) + \partial g(x)\}$ is nonempty. Then
--   $$\operatorname*{argmin}(f+g) = \operatorname{zer}\partial(f+g) = \operatorname{zer}(\partial f + \partial g).$$
--
--   The subdifferential sum rule $\partial(f+g) = \partial f + \partial g$ can fail without a qualification condition; the proposition shows that its zero sets nevertheless agree as soon as $\partial f + \partial g$ has one zero. It is used to identify $Z$ with a set of minimizers in Proposition 6.2.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero`, $f + g$ is the pointwise sum (well defined since neither function takes the value $-\infty$), and `subgrad φ x` is $\partial\varphi(x)$, empty where $\varphi(x) = +\infty$. The argmin is $\{x \mid \forall y,\ f(x) + g(x) \le f(y) + g(y)\}$.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 9, Proposition 2.7, (28)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proposition 2.7, p. 9: for `f, g ∈ Γ₀(X)` with `zer(∂f + ∂g) ≠ ∅`,
`argmin(f + g) = zer ∂(f + g) = zer(∂f + ∂g)`. -/
theorem proposition_2_7 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g x, a + b = 0) :
    {x | ∀ y, f x + g x ≤ f y + g y} = {x | (0 : X) ∈ subgrad (f + g) x} ∧
      {x | (0 : X) ∈ subgrad (f + g) x} =
        {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g x, a + b = 0} := by sorry

end InconsistentDR.Shadow
