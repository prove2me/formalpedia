-- Prove2me | Theorems.Thm_McFadden1974_MLE_rank_eq_iff_hess_negDef
-- name    : McFadden1974.MLE.rank_eq_iff_hess_negDef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:06.905179+00:00
-- url     : https://prove2.me/theorems/849019c9-6163-4263-ab3c-2ab355fee937
-- title:
--   Axiom 5 — full rank is necessary and sufficient for a negative definite Hessian
-- statement:
--   Fix $\theta \in \mathbb{R}^K$. In the conditional logit model with every trial observed ($R_n \ge 1$ for all $n$), the $\big(\sum_n J_n\big)\times K$ matrix with rows $z_{in} - \bar z_n(\theta)$ has rank $K$ if and only if the Hessian (20) at $\theta$ is negative definite:
--   $$\Big\langle \frac{\partial^2 L}{\partial\theta\,\partial\theta'}(\theta)\,\gamma,\ \gamma\Big\rangle < 0 \quad\text{for every } \gamma \ne 0.$$
--
--   This identifies the full-rank Axiom 5 as the condition for strict concavity of the log-likelihood, the analogue of the full-rank condition of the linear regression model.
--
--   **Formalization Note** The hypothesis $R_n \ge 1$ for every trial is needed: a trial with $R_n = 0$ contributes rows to the matrix but nothing to the Hessian.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), sentence before Axiom 5, and Axiom 5

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Axiom 5 is necessary and sufficient for a negative definite Hessian** (unnumbered,
sentence before Axiom 5, and Axiom 5; McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116, PDF p. 12): "A necessary and sufficient
condition for ∂²L/∂θ∂θ' to be negative definite is the following. AXIOM 5 (Full Rank). The
∑_{n=1}^N J_n × K matrix whose rows are (z_in − z̄_n) for i = 1, …, J_n and n = 1, …, N is of
rank K."

At every `θ`, the matrix with rows `z_in − z̄_n(θ)` has rank `K` if and only if the Hessian (20)
at `θ` is negative definite: `⟨H(θ)γ, γ⟩ < 0` for every `γ ≠ 0`.

**Formalization Note.** Uses the standing assumption `R_n ≥ 1` for every trial (`Data.observed`);
without it a trial with `R_n = 0` would contribute rows to the matrix but nothing to the
Hessian. -/
theorem rank_eq_iff_hess_negDef
    {K : ℕ} (d : Data K) (θ : EuclideanSpace ℝ (Fin K)) :
    (d.designMatrix θ).rank = K ↔
      ∀ γ : EuclideanSpace ℝ (Fin K), γ ≠ 0 → ⟪d.hess θ γ, γ⟫ < 0 := by sorry

end McFadden1974.MLE
