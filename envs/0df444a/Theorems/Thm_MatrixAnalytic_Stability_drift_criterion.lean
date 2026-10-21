-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_drift_criterion
-- name    : MatrixAnalytic.Stability.drift_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:40.238795+00:00
-- url     : https://prove2.me/theorems/401f58fd-baef-4d0a-a851-2307234f97ef
-- title:
--   Theorem 7.2.3 — the mean-drift criterion μ = αA₀1 − αA₂1 for positive recurrence, null recurrence and transience of a QBD
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, and assume $P$ is stochastic and irreducible. Assume the stochastic matrix $A = A_0 + A_1 + A_2$ is irreducible, and let $\alpha$ be its stationary probability vector ($\alpha \ge 0$, $\alpha\mathbf 1 = 1$, $\alpha A = \alpha$). Let
--   $$\mu = \alpha A_0 \mathbf 1 - \alpha A_2 \mathbf 1 .$$
--   Then:
--
--   1. the QBD is positive recurrent if and only if $\mu < 0$;
--   2. the QBD is null recurrent if $\mu = 0$;
--   3. the QBD is transient if $\mu > 0$.
--
--   The number $\mu$ is the mean one-step change of the level when the phase is in its stationary regime; the theorem says that stability is decided by this average drift alone, computed from $A_0$, $A_1$, $A_2$ without evaluating $G$ or $R$.
--
--   **Formalization Note** Finitely many phases is `[Fintype ι]` together with `[Nonempty ι]`. $\alpha$ is any stationary probability vector of $A$; irreducibility of $A$ makes it unique. Positive recurrence, null recurrence and transience are properties of the QBD as a Markov chain (return times of its states, computed from trajectory sums), not conditions on $G$ or $R$; each is asserted for every state.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 155, Theorem 7.2.3

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD

namespace MatrixAnalytic.Stability

/-- Theorem 7.2.3 (p. 155). Let the QBD be irreducible with finitely many phases, and let the
stochastic matrix `A = A₀ + A₁ + A₂` be irreducible, with stationary probability vector `α`.
With `μ = αA₀1 − αA₂1`: the QBD is positive recurrent iff `μ < 0`; it is null recurrent if
`μ = 0`; it is transient if `μ > 0`. -/
theorem drift_criterion {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (α : ι → ℝ) (hα : IsStationaryC (matA A₀ A₁ A₂) α) :
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔ meanDrift A₀ A₂ α < 0) ∧
    (meanDrift A₀ A₂ α = 0 → IsNullRecurrentChain (qbdP B A₀ A₁ A₂)) ∧
    (0 < meanDrift A₀ A₂ α → IsTransientChain (qbdP B A₀ A₁ A₂)) := by sorry

end MatrixAnalytic.Stability
