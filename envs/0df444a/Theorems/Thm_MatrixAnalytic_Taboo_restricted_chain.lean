-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_restricted_chain
-- name    : MatrixAnalytic.Taboo.restricted_chain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:37.100274+00:00
-- url     : https://prove2.me/theorems/a6ba4223-6be4-4963-a9aa-6f7cfdb42dd5
-- title:
--   Theorem 5.3.1 — the restricted chain on $T$ is an irreducible positive recurrent Markov chain with $P(T) = P_T + P_{TT^c}(I - P_{T^c})^{-1}P_{T^cT}$ and $\boldsymbol\pi_TP(T) = \boldsymbol\pi_T$
-- statement:
--   Let $\{X_n, n \ge 0\}$ be an irreducible, homogeneous, positive recurrent Markov chain on a countable state space $S$ with transition matrix $P$ and stationary probability vector $\boldsymbol\pi$, and let $S$ be partitioned into two subsets $T$ and $T^c$, with $T$ nonempty. Let $\tau_0 = \inf\{i \ge 0 : X_i \in T\}$, $\tau_{n+1} = \inf\{i \ge \tau_n + 1 : X_i \in T\}$, and let $X^T_n = X_{\tau_n}$ be the **restricted process**, the state visited when the chain is for the $n$-th time in $T$. Let
--   $$P(T) = P_T + P_{TT^c}(I - P_{T^c})^{-1}P_{T^cT}, \qquad (I - P_{T^c})^{-1} = \sum_{\nu \ge 0}P_{T^c}^\nu.$$
--   Then:
--
--   1. the restricted process is defined at every time: from any initial state, $\tau_0 < \infty$ almost surely;
--   2. it is a homogeneous Markov chain on $T$ with transition matrix $P(T)$: for every initial state $i \in S$ and all $j_0, \dots, j_k \in T$,
--   $$\mathrm P[X^T_0 = j_0, X^T_1 = j_1, \dots, X^T_k = j_k \mid X_0 = i] = \mathrm P[X^T_0 = j_0 \mid X_0 = i]\; P(T)_{j_0j_1}\cdots P(T)_{j_{k-1}j_k};$$
--   3. $P(T)$ is a stochastic matrix on $T$;
--   4. this chain is irreducible and every state of $T$ is positive recurrent for it;
--   5. its stationary probability vector is proportional to $\boldsymbol\pi_T$:
--   $$\boldsymbol\pi_TP(T) = \boldsymbol\pi_T,$$
--   and $\boldsymbol\pi_T/(\boldsymbol\pi_T\mathbf 1)$ is the unique stationary probability vector of $P(T)$.
--
--   The restricted (censored) chain is the device by which the stationary distribution of a chain is computed on a subset of states by itself; it underlies the matrix-geometric and the linear-level reduction methods of the later chapters.
--
--   **Formalization Note** The restricted process is encoded by its finite-dimensional law, a sum over trajectories of the original chain, so clause 2 is the full statement "the restricted process is a homogeneous Markov chain with transition matrix $P(T)$"; $P(T)$ is defined by the formula only. Irreducibility, positive recurrence (finite expected return time) and stationarity of the restricted chain are the notions of the mission applied to $P(T)$ read as a real matrix on the states of $T$; probabilities of the restricted process take values in $[0, \infty]$. The hypothesis that $T$ is nonempty is not printed; for $T = \emptyset$ there is no restricted process. Positive recurrence means every state has finite expected return time, and $\boldsymbol\pi$ is a stationary probability vector of $P$ ($\boldsymbol\pi \ge 0$, $\boldsymbol\pi\mathbf 1 = 1$, $\boldsymbol\pi P = \boldsymbol\pi$). Aperiodicity, part of the chapter's standing setting, is not assumed: the theorem lists its own hypotheses.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 118, Theorem 5.3.1 (restricted process defined on p. 118)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices
import Definitions.Def_MatrixAnalytic_Taboo_Restricted

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Theorem 5.3.1 (p. 118). Let `{X_n}` be an irreducible, homogeneous,
positive recurrent Markov chain on a countable state space `S` with transition matrix `P` and
stationary probability vector `π`, and let `S` be partitioned into `T` (nonempty) and `Tᶜ`.
The restricted process `X^T_n = X_{τ_n}` (`τ_n` the `n`-th epoch of a visit to `T`) is defined at
every `n` almost surely, and it is a homogeneous Markov chain on the state space `T` whose
transition matrix is
`P(T) = P_T + P_{TTᶜ}(I − P_{Tᶜ})⁻¹P_{TᶜT}`
(with `(I − P_{Tᶜ})⁻¹ = Σ_ν P_{Tᶜ}^ν`): for every initial state `X_0 = i` and states
`j₀, …, j_k ∈ T`,
`P[X^T_0 = j₀, …, X^T_k = j_k | X_0 = i] = P[X^T_0 = j₀ | X_0 = i] · P(T)_{j₀j₁} ⋯ P(T)_{j_{k-1}j_k}`.
`P(T)` is a stochastic matrix, the chain is irreducible and positive recurrent, and its
stationary probability vector is proportional to `π_T`: `π_T P(T) = π_T`, and
`π_T / (π_T 1)` is its unique stationary probability vector. -/
theorem restricted_chain {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (hpos : ∀ x : S, PositiveRecurrent P x)
    (π : S → ℝ) (hπ : IsStationaryC P π)
    (T : Set S) (hT : T.Nonempty) :
    -- the restricted process is defined at time 0 (hence, with the next clauses, at all times)
    (∀ i : S, HasSum (fun j : T => restrictedLaw P T i [(j : S)]) 1) ∧
    -- it is a homogeneous Markov chain with transition matrix `P(T)`
    (∀ i : S, ∀ j₀ ∈ T, ∀ js : List S, (∀ j ∈ js, j ∈ T) →
      restrictedLaw P T i (j₀ :: js) =
        restrictedLaw P T i [j₀] * chainWeight (censoredMatrix P T) j₀ js) ∧
    -- `P(T)` is stochastic on `T`
    (∀ i ∈ T, HasSum (fun j : T => censoredMatrix P T i j) 1) ∧
    -- irreducible and positive recurrent
    IrreducibleC (censoredKernel P T) ∧
    (∀ i : T, PositiveRecurrent (censoredKernel P T) i) ∧
    -- `π_T P(T) = π_T`
    (∀ j : T, HasSum (fun i : T => π i * censoredKernel P T i j) (π j)) ∧
    -- the stationary probability vector of the restricted chain is `π_T / (π_T 1)`
    IsStationaryC (censoredKernel P T) (fun i : T => π i / ∑' k : T, π k) ∧
    (∀ μ : T → ℝ, IsStationaryC (censoredKernel P T) μ →
      μ = fun i : T => π i / ∑' k : T, π k) := by sorry

end MatrixAnalytic.Taboo
