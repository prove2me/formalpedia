-- Prove2me | Theorems.Thm_KallenbergLP_Transient_fiveEquivalentCharacterizations
-- name    : KallenbergLP.Transient.fiveEquivalentCharacterizations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:37:39.597951+00:00
-- url     : https://prove2.me/theorems/756eb30b-818d-4d54-9c12-7620aaf1da85
-- title:
--   Theorem 3.2.4 — five equivalent characterizations of transience
-- statement:
--   Fix strictly positive right-hand sides $\beta_j$ for the linear program. In a finite substochastic Markov decision model, the following five statements are equivalent:
--
--   1. Every pure stationary policy is transient.
--   2. Every policy, including every history-dependent randomized policy, is transient.
--   3. $\max_{i\in E}y_i^N<1$, where $N=|E|$ and $y^t$ is the survival recursion of Lemma 3.2.2.
--   4. There are $\mu_i>0$ and $0\le c<1$ with $\sum_jp_{iaj}\mu_j\le c\mu_i$ for every $i$ and $a\in A(i)$.
--   5. The program
--
--      $$\max\Big\{\sum_{i,a}x_{ia}:\ \sum_{i,a}(\delta_{ij}-p_{iaj})x_{ia}\le\beta_j\ (j\in E),\ x_{ia}\ge0\Big\}$$
--
--      has an attained finite optimum.
--
--   This characterizes transience through policy behavior, a finite-horizon survival test, a contraction inequality, and linear programming.
--
--   **Formalization Note** The strict inequality in item 3 is stated for every state, equivalent to the maximum form because the state space is nonempty and finite. Lean states four adjacent equivalences, which jointly express equivalence of all five conditions.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 42–43, Theorem 3.2.4

import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.4: five characterizations of a transient dynamic program. -/
theorem fiveEquivalentCharacterizations
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ) (hβ : ∀ j, 0 < β j) :
    ((∀ f : PureRule M, IsTransient M (purePolicy M f)) ↔
       (∀ R : Policy M, IsTransient M R)) ∧
    ((∀ R : Policy M, IsTransient M R) ↔
       (∀ i : Fin N, survivalIterate M N i < 1)) ∧
    ((∀ i : Fin N, survivalIterate M N i < 1) ↔ Contracting M) ∧
    (Contracting M ↔ LPFinite M β) := by sorry

end KallenbergLP.Transient
