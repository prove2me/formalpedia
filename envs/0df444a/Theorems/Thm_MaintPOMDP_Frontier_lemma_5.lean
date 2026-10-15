-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_lemma_5
-- name    : MaintPOMDP.Frontier.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:09.088929+00:00
-- url     : https://prove2.me/theorems/40220559-64e8-48c9-9eaf-6fb2c1606a76
-- title:
--   Lemma 5, p. 25 — inspection enters iff g^I(u†_F) + β(p_0′u†_{m†}, p_1′u†_0)′ is not dominated by U†
-- statement:
--   Under the standing assumptions, assume
--   $$c^R<\frac{c^P+\beta\gamma_1c^F}{1-\beta+\beta(\gamma_0+\gamma_1)} .$$
--   Let $(U^\dagger,u^\dagger_F)$ be the optimal solution of the two-action model $\{P,R\}$ and $(U^*,u^*_F)$ that of the three-action model $\{P,I,R\}$. Then inspection enters the optimal solution — the three-action value $\min_{U^*}\boldsymbol\pi'\mathbf u$ is strictly below the two-action value $\min_{U^\dagger}\boldsymbol\pi'\mathbf u$ for some belief $\boldsymbol\pi\ge0$ — if and only if the point
--   $$\mathbf g^I(u^\dagger_F)+\beta\begin{pmatrix}\min_{\mathbf u\in U^\dagger}\mathbf p_0'\mathbf u\\ \min_{\mathbf u\in U^\dagger}\mathbf p_1'\mathbf u\end{pmatrix}$$
--   is not dominated by $U^\dagger$, i.e. there is $\boldsymbol\pi$ in the simplex with $\boldsymbol\pi'\mathbf z<\min_{U^\dagger}\boldsymbol\pi'\mathbf u$.
--
--   This lemma reduces the three-action problem to a single test on the two-action solution of Theorem 1.
--
--   **Formalization Note** The paper's "$\mathbf u^I_0\in U^*$" is rendered as "$U^*\ne U^\dagger$ at the value level", which is equivalent by the lemma's own proof (EC p. 14). $\mathbf p_0'\mathbf u^\dagger_{m^\dagger}$ and $\mathbf p_1'\mathbf u^\dagger_0$ are the minima of $\mathbf p_0'\mathbf u$ and $\mathbf p_1'\mathbf u$ over $U^\dagger$ (p. 25 defines $m^\dagger$ as the index attaining the first). Optimal solutions are value-iteration limits as in Theorem 1.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 25, Lemma 5; proof EC p. 14

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Lemma 5 (p. 25), value form: assume c^R < thrP. Let (U†, u†_F) solve the {P, R} model and
(U*, u*_F) the {P, I, R} model. Then the three-action value is strictly below the two-action value
at some belief (i.e. inspection enters, u^I_0 ∈ U*) iff the point
g^I(u†_F) + β (min_{U†} p0′u, min_{U†} p1′u)′ is not dominated by U†. -/
theorem lemma_5 (M : Params) (hM : M.Standing) (hcR : M.cR < M.thrP)
    (Udag Ustar : Finset Vec) (uFdag uFstar : ℝ)
    (hdag : M.Solves ActSet.PR Udag uFdag) (hstar : M.Solves ActSet.PIR Ustar uFstar) :
    (∃ π : Vec, 0 ≤ π 0 ∧ 0 ≤ π 1 ∧ minDot Ustar π < minDot Udag π) ↔
      ¬ Dominated (M.gI uFdag + M.β • ![minDot Udag M.p0, minDot Udag M.p1]) Udag := by sorry

end MaintPOMDP.Frontier
