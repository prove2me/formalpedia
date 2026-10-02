-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_transaction_cost_upper_bounding_function
-- name    : MDPFinance.MeanVariance.transaction_cost_upper_bounding_function
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:03.08875+00:00
-- url     : https://prove2.me/theorems/4f29c0ca-fe6c-4b90-814e-eebc10916ce5
-- title:
--   Proposition 4.5.1 — an upper bounding function for the transaction-cost model
-- statement:
--   The function $b(x_0,x_1) := 1+x_0+x_1$ is an **upper bounding function** for the
--   transaction-cost Markov Decision Model (Definition 2.4.1): there exist constants $c_r,c_g,\alpha_b
--   \ge0$ with (i) $r_n^+\le c_r\,b$ (trivial here, since $r_n\equiv0$), (ii) $U^+\le c_g\,b$, and
--   (iii) $\mathbb{E}\big[b\big(h(x,a)(1+i_{n+1}),\,a\,\tilde R_{n+1}\big)\big] \le
--   \alpha_b\,b(x)$ for every admissible post-transaction holding $a$.
--
--   This is the entry point of the chapter's argument: an upper bounding function is what lets the
--   Structure Theorem's machinery (chunk `02a`/`02b`) apply to a value function that need not be
--   bounded outright. The book proves (ii) by citing that "any concave function can be bounded from
--   above by an affine-linear function" — carried here as the explicit hypothesis `hU_affine`, since
--   no general Mathlib lemma of that shape was found for this domain.
--
--   **Formalization Note.** `hU_affine` and integrability of $\tilde R_{n+1}$ are added as explicit
--   hypotheses rather than derived, matching the book's own proof, which invokes the affine-bound fact
--   as already established rather than proving it inline.
--
--   **Formalization Note (moderation).** The affine bound on the concave utility and the
--   integrability of $\tilde R_{n+1}$ are consequences of the model's assumptions (concavity,
--   (FM)(ii)), not hypotheses; the bounds are stated on the state space $E$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 107, PDF 121, Proposition 4.5.1

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Proposition 4.5.1 (Bäuerle–Rieder, p. 107, PDF 121). Under the section's standing
Assumption (FM) (carried by the model), the function `b(x) := 1+x0+x1` is an upper bounding
function for the transaction-cost Markov Decision Model: there exist `c_r, c_g, α_b ≥ 0` with (i)
`r_n^+ ≤ c_r b` (trivial, `r_n ≡ 0`); (ii) `U^+(x0+x1) ≤ c_g b(x)` on `E`; (iii)
`𝔼[b(h(x,a)(1+i_{n+1}), a\,\tilde R_{n+1})] ≤ α_b b(x)` for `x ∈ E` and `a` in the admissible
range. -/
theorem transaction_cost_upper_bounding_function {Ω : Type*} [MeasurableSpace Ω]
    (M : TransactionCostMarket Ω) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ x ∈ Estate, max (0 : ℝ) 0 ≤ cr * (1 + x.1 + x.2)) ∧
      (∀ x ∈ Estate, max (M.U (x.1 + x.2)) 0 ≤ cg * (1 + x.1 + x.2)) ∧
      (∀ n < M.N, ∀ x ∈ Estate, ∀ a ∈ M.Arange x.1 x.2,
        (∫ ω, (1 + M.h x.1 x.2 a * (1 + M.i (n + 1)) + a * M.Rtilde (n + 1) ω) ∂M.measIP) ≤
          αb * (1 + x.1 + x.2)) := by sorry

end MDPFinance.MeanVariance
