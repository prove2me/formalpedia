-- Prove2me | Theorems.Thm_KallenbergLP_Transient_survivalIterate_eq_max_survival
-- name    : KallenbergLP.Transient.survivalIterate_eq_max_survival
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:37:18.0439+00:00
-- url     : https://prove2.me/theorems/3a5dace0-e601-41dd-a60a-5c9b38040aa5
-- title:
--   Lemma 3.2.2 — maximal finite-horizon survival probability
-- statement:
--   Let $y^0_i=1$ and $y^t_i=\max_{a\in A(i)}\sum_jp_{iaj}y_j^{t-1}$. For each $t\ge1$, choose a pure rule $f_t$ that attains the maximum in every state and use the policy $R_t=(f_t,f_{t-1},\ldots,f_1,f_1,\ldots)$; let $R_0$ be arbitrary. Then, for every state $i$ and $t\ge0$,
--
--   $$y_i^t=\sum_jP_{R_t}(X_{t+1}=j\mid X_1=i)=\sup_R\sum_jP_R(X_{t+1}=j\mid X_1=i).$$
--
--   This identifies the recursion with the greatest survival probability over the full policy class. Lean states attainment and the upper bound against each policy, which together assert the displayed supremum.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 41–42, Lemma 3.2.2

import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Lemma 3.2.2, including attainment by the specified reverse sequence of pure rules. -/
theorem survivalIterate_eq_max_survival
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (f : ℕ → PureRule M) (R₀ : Policy M)
    (hf : ∀ t : ℕ, 0 < t → ∀ i : Fin N,
      survivalIterate M t i =
        ∑ j : Fin N, M.transition i ((f t).choose i) j * survivalIterate M (t - 1) j) :
    ∀ (t : ℕ) (i : Fin N),
      survivalIterate M t i = survivalProb M (extremalPolicy M f R₀ t) i t ∧
        ∀ R : Policy M, survivalProb M R i t ≤ survivalIterate M t i := by sorry

end KallenbergLP.Transient
