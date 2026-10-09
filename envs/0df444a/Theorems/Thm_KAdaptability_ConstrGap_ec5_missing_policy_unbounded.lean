-- Prove2me | Theorems.Thm_KAdaptability_ConstrGap_ec5_missing_policy_unbounded
-- name    : KAdaptability.ConstrGap.ec5_missing_policy_unbounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:49.199977+00:00
-- url     : https://prove2.me/theorems/b8a35c71-b4e3-4b8a-92f3-58f6b4721bca
-- title:
--   Proof of Theorem 4, (EC.5) — policies missing some y⋆ ∈ {0,1}^Q give objective +∞
-- statement:
--   Let $Q,K\in\mathbb N$ and consider the K-adaptability problem (EC.5) associated with the instance (EC.4) of $\mathcal P$ (no first-stage decision, $\mathcal Y=\{0,1\}^Q$, zero objective, constraints $y_q-\xi_q\le\frac12$, $\xi_q-y_q\le\frac12$, uncertainty set $[0,1]^Q$). Let $y^1,\dots,y^K\in\{0,1\}^Q$ be policies and suppose some $y^\star\in\{0,1\}^Q$ differs from every $y^k$. Then the objective of (EC.5) at these policies is $+\infty$:
--   $$\sup_{\xi\in[0,1]^Q}\ \inf_{k\in\mathcal K}\{0 : y^k_q-\xi_q\le\tfrac12,\ \xi_q-y^k_q\le\tfrac12,\ q=1,\dots,Q\}=+\infty.$$
--
--   The reason, as on the page, is the parameter realization $\xi=y^\star$, at which no policy $y^k$ is feasible. This is the per-decision step of the proof of Theorem 4.
--
--   **Formalization Note** The objective is the general K-adaptability objective $f_K$ of `KAdaptability.ConstrGap.Values` at the instance `inst Q`, with the first-stage decision the unique point of $\mathbb R^0$. An empty infimum equals $+\infty$ (p. 8). The policies are a family indexed by `Fin K`; repetitions are allowed.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec5 (PDF p. 39), Proof of Theorem 4, (EC.5), the sentence beginning "In fact, assume that a solution"

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

open Matrix

namespace KAdaptability.ConstrGap

/-- Proof of Theorem 4, p. ec5: if the policies `y¹, …, y^K ∈ {0,1}^Q` of the K-adaptability
problem (EC.5) associated with (EC.4) miss some `y⋆ ∈ {0,1}^Q`, the objective of (EC.5) at
these policies is `+∞`. -/
theorem ec5_missing_policy_unbounded (nQ K : ℕ) (x : Fin 0 → ℝ) (ys : Fin K → Fin nQ → ℝ)
    (hys : ∀ k, ys k ∈ (inst nQ).Y) (ystar : Fin nQ → ℝ) (hstar : ystar ∈ (inst nQ).Y)
    (hmiss : ∀ k, ys k ≠ ystar) :
    (inst nQ).objPK K x ys = ⊤ := by sorry

end KAdaptability.ConstrGap
