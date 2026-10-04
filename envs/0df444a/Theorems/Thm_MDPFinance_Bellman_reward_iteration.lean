-- Prove2me | Theorems.Thm_MDPFinance_Bellman_reward_iteration
-- name    : MDPFinance.Bellman.reward_iteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:13:17.029473+00:00
-- url     : https://prove2.me/theorems/cde05f0a-e72f-4c66-aa79-5a33d4b786ca
-- title:
--   Theorem 2.3.4 — Reward Iteration
-- statement:
--   Fix an $N$-stage policy $\pi = (f_0,\dots,f_{N-1})$. The value of $\pi$ can be computed
--   recursively, backward from the terminal time: $V_N^\pi = g_N$, and for every
--   $n = 0, \dots, N-1$,
--
--   $$
--   V_n^\pi = T_n^{f_n} V_{n+1}^\pi,
--   $$
--
--   so that unwinding the recursion all the way to the terminal time gives
--
--   $$
--   V_n^\pi = T_n^{f_n}\, T_{n+1}^{f_{n+1}} \cdots T_{N-1}^{f_{N-1}}\, g_N.
--   $$
--
--   This connects the value $V_n^\pi(x)$ — defined as an expectation of the total future reward
--   under the process started at $(n,x)$ — to a purely recursive, one-step-at-a-time computation via
--   the operators of Definition 2.3.1. It is the operational tool behind every later use of the
--   value function: the Bellman equation for the *optimal* value function $V_n$ (Theorem 2.3.8) is
--   the same recursion with $T_n^{f_n}$ replaced by the supremum operator $T_n$, and Reward Iteration
--   is what makes that replacement meaningful (evaluating a candidate policy along the way).
--
--   **Formalization Note.** $V_n^\pi$ is built from an accumulator-style recursion over the kernels
--   $Q_k$ (see `MDPFinance.Bellman.V`'s natural-language statement), not defined directly via
--   $T_n^{f_n}$; consequently both parts of this theorem are genuine (if short) consequences of
--   linearity of the integral rather than definitional unfoldings — see `MODERATION_NOTES.md`.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.2, which
--   the book assumes throughout, is carried as the explicit hypothesis `hAN`; without it the
--   expectations defining $V_n^\pi$ need not exist, and the extended-real integral's convention
--   for $\infty - \infty$ would make the statement's terms artefacts of that convention.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 20, Theorem 2.3.4

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.4 (Reward Iteration; Bäuerle–Rieder, p. 20, PDF 35), under the standing
Integrability Assumption (AN) of Section 2.2. Let `π = (f_0,…,f_{N-1})` be
an `N`-stage policy. For `n = 0,…,N-1` it holds: a) `V_N^π = g_N` and
`V_n^π = T_n^{f_n} V_{n+1}^π`; b) `V_n^π = T_n^{f_n} ⋯ T_{N-1}^{f_{N-1}} g_N`. -/
theorem reward_iteration {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M) (π : Policy M) :
    (∀ x, Vpi M π N x = (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, Vpi M π n x = Tf M n (Vpi M π (n + 1)) (π.1 n) x) ∧
    (∀ n ≤ N, ∀ x, Vpi M π n x = TfChain M π (N - n) n (fun x => (M.g x : EReal)) x) := by sorry

end MDPFinance.Bellman
