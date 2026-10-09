-- Prove2me | Theorems.Thm_KAdaptability_ConstrGap_theorem_4
-- name    : KAdaptability.ConstrGap.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:46.336018+00:00
-- url     : https://prove2.me/theorems/8a032c70-d571-42fe-be14-22f877d0233f
-- title:
--   Theorem 4 — under constraint uncertainty, 𝒫_K can be strictly worse than 𝒫 for every K < |𝒴|
-- statement:
--   **Theorem 4.** The K-adaptability problem $\mathcal P_K$ may attain a strictly higher optimal value than the two-stage robust binary program $\mathcal P$ for any number of policies $K<|\mathcal Y|$.
--
--   Precisely: for every $Q\in\mathbb N$, let (EC.4) be the instance of $\mathcal P$ with no first-stage decision, second-stage feasible set $\mathcal Y=\{0,1\}^Q$ (so $|\mathcal Y|=2^Q$), zero objective, second-stage constraints $y_q-\xi_q\le\frac12$, $\xi_q-y_q\le\frac12$ ($q=1,\dots,Q$), and uncertainty set $[0,1]^Q$. Then for **every** $K<|\mathcal Y|$,
--   $$\operatorname{opt}(\mathcal P)\ <\ \operatorname{opt}(\mathcal P_K)\qquad\text{for the instance (EC.4).}$$
--
--   Contrast Theorem 1 of the same paper: when $\xi$ enters only the objective, $\min\{\dim\mathcal Y,\operatorname{rk}Q\}+1$ policies already attain the optimal value of $\mathcal P$. Theorem 4 shows that when $\xi$ enters the constraints, every feasible policy $y\in\mathcal Y$ may be required.
--
--   **Formalization Note** $\mathcal P$ and $\mathcal P_K$ are the general problems of `KAdaptability.ConstrGap.Values` (any dimensions, any data), evaluated at the instance `inst Q` of `KAdaptability.ConstrGap.Instance`; the affine right-hand side of (EC.4) is encoded with an auxiliary parameter $\xi_{Q+1}=1$, as the paper prescribes on p. 6. The instance is fixed before $K$ is chosen, so a single instance works for all $K<|\mathcal Y|$. Values are in `EReal`.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 15, Theorem 4; proof on p. ec5 (PDF p. 39)

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

open Matrix

namespace KAdaptability.ConstrGap

/-- Theorem 4, p. 15: the K-adaptability problem 𝒫_K may attain a strictly higher optimal value
than the two-stage robust binary program 𝒫 for any number of policies `K < |𝒴|`. For every
`Q`, the instance (EC.4) (`𝒴 = {0,1}^Q`) has `opt(𝒫) < opt(𝒫_K)` for every `K < |𝒴|`. -/
theorem theorem_4 (nQ K : ℕ) (hK : K < (inst nQ).Y.card) :
    (inst nQ).optP < (inst nQ).optPK K := by sorry

end KAdaptability.ConstrGap
