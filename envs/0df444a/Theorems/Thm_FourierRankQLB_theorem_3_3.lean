-- Prove2me | Theorems.Thm_FourierRankQLB_theorem_3_3
-- name    : FourierRankQLB.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:46.737517+00:00
-- url     : https://prove2.me/theorems/138d8d9a-9f01-4879-93fc-8dd7a53f4d84
-- title:
--   Theorem 3.3 — the Fourier-rank polynomial method
-- statement:
--   Consider a $T$-query algorithm of the form (15) on a Hilbert space $H$, with query families $\{O_{Q,j}\}$. Suppose the $j$th query has Fourier-rank cost at most $s_j$, and put $R=\sum_{j=1}^Ts_j$.
--
--   1. The final state, as a function of $Q$, lies in $V_R^{(n)}\mathbin{\widehat\otimes}H$.
--   2. Every final outcome probability $Q\mapsto\langle\psi_T(Q),E\,\psi_T(Q)\rangle$, $0\preceq E\preceq I$, belongs to $A_{2R}^{(n)}$.
--   3. If $F:O(n)\to\{-1,+1\}$ is measurable with
--   $$
--   \int_{O(n)}F(Q)f(Q)\,d\mu_n(Q)=0\quad\text{for every }f\in A_{2R}^{(n)},
--   $$
--   then any prediction in $\{-1,+1\}$ has Haar-average success probability for $F(Q)$ exactly $1/2$.
--
--   This is the reusable core of the method. It separates the cost of a query from the choice of target function.
--
--   Differences from the source:
--
--   - encoding: the algorithm has a purification whose final state lies in $V_R\mathbin{\widehat\otimes}H_{alg}$ → the final state of the form (15) lies in it; reason: the form (15) is the purified form, by p.16
--   - encoding: the algorithm outputs a prediction in $\{-1,+1\}$ → a POVM on `Bool`, with `true` coding $+1$; reason: a two-outcome measurement is exactly such a POVM
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 3.3, p.18

import Mathlib
import Definitions.Def_FourierRankQLB_QueryCircuit_finalState
import Definitions.Def_FourierRankQLB_HasFourierRankCost
import Definitions.Def_FourierRankQLB_Ar
import Definitions.Def_FourierRankQLB_POVM_prob
import Definitions.Def_FourierRankQLB_boolSign

open MeasureTheory

namespace FourierRankQLB

/-- Theorem 3.3 (Fourier-rank polynomial method). Consider a `T`-query algorithm of the form (15) whose
`j`th query has Fourier-rank cost at most `s_j`, and put `R = ∑ s_j`. Its final state lies in
`V_R ⊗̂ H_alg`, and every final outcome probability belongs to `A_{2R}`. If moreover
`F : O(n) → {-1, +1}` is measurable and satisfies (22), then every prediction of `F(Q)` in `{-1, +1}`
has Haar-average success probability exactly `1/2`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 3.3, p. 18.

**Formalization Note.** The form (15) is already purified, so its final state is the purification of
the statement. `O Q j` is the oracle of the `j`th slot at `Q`, a general family. A final outcome
probability is `⟨ψ_T(Q), E ψ_T(Q)⟩` for an effect `0 ⪯ E ⪯ I`. A prediction is a two-outcome POVM on
`Bool`, with `true` coding `+1`; it succeeds at `Q` on the outcome coding `F(Q)`. -/
theorem theorem_3_3 {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (C : QueryCircuit H) (O : Od n → Fin C.T → (H ≃ₗᵢ[ℂ] H))
    (s : Fin C.T → ℕ) (hO : ∀ j, HasFourierRankCost (fun Q => O Q j) (s j)) :
    (∃ Φ ∈ VH n (∑ j, s j) H, Φ =ᵐ[haarO n] fun Q => C.finalState (O Q)) ∧
    (∀ E : H →L[ℂ] H, E.IsPositive → (1 - E).IsPositive →
      ∃ f ∈ Ar n (2 * ∑ j, s j), f =ᵐ[haarO n]
        fun Q => inner ℂ (C.finalState (O Q)) (E (C.finalState (O Q)))) ∧
    (∀ F : Od n → ℝ, Measurable F → (∀ Q, F Q = 1 ∨ F Q = -1) →
      (∀ f ∈ Ar n (2 * ∑ j, s j), ∫ Q, (F Q : ℂ) * f Q ∂haarO n = 0) →
      ∀ M : POVM Bool H,
        ∫ Q, M.prob (C.finalState (O Q)) {b | boolSign b = F Q} ∂haarO n = 1 / 2) := by sorry

end FourierRankQLB
