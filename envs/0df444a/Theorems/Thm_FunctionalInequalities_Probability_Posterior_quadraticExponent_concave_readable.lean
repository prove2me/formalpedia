-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_quadraticExponent_concave_readable
-- name    : FunctionalInequalities.Probability.Posterior.quadraticExponent_concave_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:22.720522+00:00
-- url     : https://prove2.me/theorems/c00cf1d3-34cb-42b3-91ca-1ba2574014a2
-- title:
--   Concavity of the Linear–Quadratic Posterior Exponent
-- statement:
--   This statement establishes concavity of the linear–quadratic exponent used for posterior tilting.
--
--   Let $E$ be a real inner-product space, $c\in E$, and $Q:E\to E$ a continuous linear map. Assume:
--
--   1. $Q$ is symmetric: $\langle Qu,v\rangle=\langle u,Qv\rangle$ for all $u,v\in E$.
--   2. $Q$ is positive semidefinite: $\langle Qx,x\rangle\ge0$ for every $x\in E$.
--
--   For `quadraticExponent` defined by
--
--   $$
--   \operatorname{quadraticExponent}(c,Q)(x)=\langle c,x\rangle-\frac12\langle Qx,x\rangle,
--   $$
--
--   this function is concave on all of $E$:
--
--   $$
--   \operatorname{ConcaveOn}(\mathbb{R},E,\operatorname{quadraticExponent}(c,Q)).
--   $$
--
--   The result supplies the concavity condition needed to show that the associated linear–quadratic posterior is log-concave.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem quadraticExponent_concave (c : E) (Q : E →L[ℝ] E)
--       (hSym : ∀ u v : E, ⟪Q u, v⟫ = ⟪u, Q v⟫)
--       (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : ConcaveOn ℝ univ (quadraticExponent c Q)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   [Source excerpt, lines 59–61](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean#L59-L61) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean#L57-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Exponent`, declaration `FunctionalInequalities.Probability.Posterior.quadraticExponent_concave`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open Set

theorem FunctionalInequalities.Probability.Posterior.quadraticExponent_concave_readable (c : E) (Q : E →L[ℝ] E)
    (hSym : ∀ u v : E, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : ConcaveOn ℝ univ (quadraticExponent c Q) := by sorry
