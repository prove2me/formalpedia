-- Prove2me | Theorems.Thm_KAdaptability_ConstrGap_ec5_unbounded
-- name    : KAdaptability.ConstrGap.ec5_unbounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:06.752342+00:00
-- url     : https://prove2.me/theorems/7e60a720-2404-4733-b375-e1388d0ccb5a
-- title:
--   Proof of Theorem 4, (EC.5) — the K-adaptability problem of (EC.4) is unbounded for K < |𝒴| = 2^Q
-- statement:
--   Let $Q\in\mathbb N$ and consider the instance (EC.4) of $\mathcal P$, whose second-stage feasible set is $\mathcal Y=\{0,1\}^Q$, so $|\mathcal Y|=2^Q$. For every number of policies $K<|\mathcal Y|$, the associated K-adaptability problem
--   $$\text{(EC.5)}\qquad \inf_{y^1,\dots,y^K\in\{0,1\}^Q}\ \sup_{\xi\in[0,1]^Q}\ \inf_{k\in\mathcal K}\{0 : y^k_q-\xi_q\le\tfrac12,\ \xi_q-y^k_q\le\tfrac12,\ q=1,\dots,Q\}$$
--   has optimal value $+\infty$.
--
--   Together with the fact that (EC.4) itself has optimal value $0$, this shows that no number of policies smaller than $|\mathcal Y|$ suffices for this instance.
--
--   **Formalization Note** The optimal value is the general $\operatorname{opt}(\mathcal P_K)$ of `KAdaptability.ConstrGap.Values` at the instance `inst Q`, in `EReal`; "unbounded" means the value $\top=+\infty$. The hypothesis is $K<|\mathcal Y|$ for the instance's `Finset` $\mathcal Y$, whose cardinality is $2^Q$ (`binaryCube_card`).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec5 (PDF p. 39), Proof of Theorem 4, (EC.5)

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

open Matrix

namespace KAdaptability.ConstrGap

/-- Proof of Theorem 4, p. ec5: the K-adaptability problem (EC.5) associated with (EC.4) is
unbounded (optimal value `+∞`) whenever `K < |𝒴| = 2^Q`. -/
theorem ec5_unbounded (nQ K : ℕ) (hK : K < (inst nQ).Y.card) :
    (inst nQ).optPK K = ⊤ := by sorry

end KAdaptability.ConstrGap
