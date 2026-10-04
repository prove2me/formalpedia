-- Prove2me | Theorems.Thm_MDPFinance_Bellman_verification_theorem
-- name    : MDPFinance.Bellman.verification_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:15:23.2725+00:00
-- url     : https://prove2.me/theorems/5283c8f3-d155-4caa-b4a6-b406728ffcf2
-- title:
--   Theorem 2.3.7 — the Verification Theorem
-- statement:
--   Suppose $(v_n)_{n=0}^N \subseteq \mathrm{IM}(E)$ is *any* sequence solving the Bellman equation,
--   $v_N = g_N$ and $v_n = T_n v_{n+1}$ for $n = 0,\dots,N-1$ — without assuming a priori that
--   $v_n$ equals the value function $V_n$. Then:
--
--   1. $v_n \ge V_n$ for every $n = 0,\dots,N$;
--   2. if, in addition, $f_n^*$ is a maximizer of $v_{n+1}$ for every $n = 0,\dots,N-1$, then in fact
--      $v_n = V_n$ for every $n$, and the policy $\pi^* = (f_0^*,\dots,f_{N-1}^*)$ built from these
--      maximizers is optimal for the $N$-stage Markov Decision Problem.
--
--   The first part is an easy monotone-comparison argument; the second is the substantive claim
--   that *any* solution of the Bellman equation together with maximizers already pins down the true
--   value function and produces an optimal policy — without appealing to the Structure Assumption
--   (SAN) or to any existence argument for $(v_n)$ itself. This theorem is what makes the Structure
--   Theorem's abstract existence claim (Theorem 2.3.8) usable in practice: in applications one
--   typically *guesses* a candidate solution of the Bellman equation (e.g. of a particular
--   parametric form) and only needs the Verification Theorem, not the general existence machinery,
--   to confirm it is correct.
--
--   **Formalization Note.** "$(v_n)$ is a solution of the Bellman equation" is formalized as three
--   explicit hypotheses (`v n ∈ IM E` for every `n`, `v N = g_N`, and `v n = T_n (v (n+1))` for
--   `n < N`) rather than a bundled definition, since this notion is used nowhere else in this
--   mission.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.2, which
--   the book assumes throughout, is carried as the explicit hypothesis `hAN`; without it the
--   expectations defining $V_n^\pi$ need not exist, and the extended-real integral's convention
--   for $\infty - \infty$ would make the statement's terms artefacts of that convention.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 22, Theorem 2.3.7

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.7 (Verification Theorem; Bäuerle–Rieder, p. 22, PDF 37), under the standing
Integrability Assumption (AN). Let `(v_n) ⊆ IM(E)`,
`n = 0,…,N`, be a solution of the Bellman equation (`v_N = g_N`, `v_n = T_n v_{n+1}` for
`n = 0,…,N-1`). Then a) `v_n ≥ V_n` for `n = 0,…,N`. b) If `f_n^*` is a maximizer of `v_{n+1}`
for `n = 0,…,N-1`, then `v_n = V_n` for every `n`, and the policy
`π^* = (f_0^*,…,f_{N-1}^*)` is optimal for the `N`-stage Markov Decision Problem. -/
theorem verification_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (v : ℕ → E → EReal) (hv_IM : ∀ n, v n ∈ IM E)
    (hv_N : v N = fun x => (M.g x : EReal)) (hv_bellman : ∀ n < N, v n = T M n (v (n + 1))) :
    (∀ n ≤ N, ∀ x, V M n x ≤ v n x) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (v (n + 1)) (fstar.1 n)) →
        (∀ n ≤ N, v n = V M n) ∧ Vpi M fstar 0 = V M 0) := by sorry

end MDPFinance.Bellman
