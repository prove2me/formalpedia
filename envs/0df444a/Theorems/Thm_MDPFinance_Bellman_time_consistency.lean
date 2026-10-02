-- Prove2me | Theorems.Thm_MDPFinance_Bellman_time_consistency
-- name    : MDPFinance.Bellman.time_consistency
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:18:51.375087+00:00
-- url     : https://prove2.me/theorems/b354c75a-d2fd-41fd-b639-c0c92a5274fb
-- title:
--   Theorem 2.3.12 — the Principle of Dynamic Programming
-- statement:
--   This theorem makes precise the informal Principle of Dynamic Programming: an optimal policy,
--   once found, is optimal not only from the start but from every later time it might reach.
--   Formally, under the Structure Assumption (SAN), for $n \le m \le N$: if a fixed policy $\pi^*$
--   attains the value function at $(n,x)$, i.e. $V_n^{\pi^*}(x) = V_n(x)$, then $\pi^*$ also attains
--   the value function at time $m$, $\mathbb{P}^{\pi^*}_{n,x}$-almost surely:
--
--   $$
--   V_n^{\pi^*}(x) = V_n(x) \ \Longrightarrow \ V_m^{\pi^*} = V_m \quad
--   \mathbb{P}^{\pi^*}_{n,x}\text{-a.s.}
--   $$
--
--   Equivalently: if $(f_n^*,\dots,f_{N-1}^*)$ is optimal for the sub-problem on $[n,N]$, then its
--   tail $(f_m^*,\dots,f_{N-1}^*)$ is optimal for the sub-problem on $[m,N]$. This is what licenses
--   the whole backward-induction solution method: an optimal policy can be assembled stage by stage
--   without ever having to reconsider earlier stages once later ones are fixed. The proof combines
--   Reward Iteration (Theorem 2.3.4) with the flow property (Corollary 2.3.9) and an equality case
--   of an inequality chain.
--
--   **Formalization Note.** "$\mathbb{P}^{\pi^*}_{n,x}$-almost surely" is stated with respect to
--   `stepKernel M pistar n m x`, the law of $X_m$ given $X_n = x$ under $\pi^*$ (built from the
--   one-step kernels of the policy alone), rather than the full canonical path measure on
--   $\Omega = E^{N+1}$, which this mission does not construct — the conclusion only ever depends on
--   $X_m$, so the two are equivalent. See `MDPFinance.Bellman.ValueFunction`'s natural-language
--   statement and `MODERATION_NOTES.md`.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.2, which
--   the book assumes throughout, is carried as the explicit hypothesis `hAN`; without it the
--   expectations defining $V_n^\pi$ need not exist, and the extended-real integral's convention
--   for $\infty - \infty$ would make the statement's terms artefacts of that convention.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 26, Theorem 2.3.12

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_MDPFinance_Bellman_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Theorem 2.3.12 (Principle of Dynamic Programming; Bäuerle–Rieder, p. 26, PDF 41), under the
standing Integrability Assumption (AN): let (SAN) be satisfied. Then for `n ≤ m ≤ N`: if `V_n^{π^*}(x) = V_n(x)`, then `V_m^{π^*} = V_m`
`ℙ^{π^*}_{n,x}`-almost surely, i.e. if `(f_n^*,…,f_{N-1}^*)` is optimal for the time period
`[n,N]` then `(f_m^*,…,f_{N-1}^*)` is optimal for `[m,N]`. The a.s. statement is w.r.t. the law
of `X_m` given `X_n = x` under `π^*` (`stepKernel M pistar n m x`), rather than the full
canonical path measure on `Ω = E^{N+1}`, which this chunk does not construct — see
`MODERATION_NOTES.md`. -/
theorem time_consistency {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) (pistar : Policy M) (n m : ℕ) (hnm : n ≤ m)
    (hm : m ≤ N) (x : E) (hopt : Vpi M pistar n x = V M n x) :
    ∀ᵐ x' ∂(stepKernel M pistar n m x), Vpi M pistar m x' = V M m x' := by sorry

end MDPFinance.Bellman
