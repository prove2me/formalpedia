-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_equal_energy_reduction
-- name    : GaussianBCSecondOrder.equal_energy_reduction
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:32:25.119001+00:00
-- url     : https://prove2.me/theorems/395209bf-5064-4b61-8eca-e99d118cfca9
-- title:
--   Lemma 7: reduction to equal-energy codewords
-- statement:
--   This lemma allows the converse proof to assume that all codewords have the same energy.
--
--   Let $S_1>S_2>0$ and $\rho\in[-1,1]$.
--
--   **Lemma.** Every length-$n$ code satisfying the power constraint $\|x^n(m_1,m_2)\|^2\le n$ induces a length-$N$ code, $N=n+1$, for the same channel, with the same message sizes, with every conditional error probability unchanged, and such that all codewords have squared norm exactly $N$. For sequences of codes, the first- and second-order coding rates of eq. (16) are unchanged.
--
--   The induced code appends the coordinate $\sqrt{N-\|x^n(m_1,m_2)\|^2}$ to each codeword, so after relabeling the blocklength one may assume $\|x^n(m_1,m_2)\|^2=n$ for all message pairs.
--
--   **Formalization Note** The Lean statement has two clauses. The first is the existence, for every $(n,M_1,M_2)$-code, of an $(n+1,M_1,M_2)$-code with identical conditional error probabilities and all codewords of squared norm $n+1$. The second renders "the coding rates are unchanged" as the identity, for every message-size sequence $(M_n)$ and every $R\in\mathbb R$,
--   $$\liminf_{n\to\infty}\frac{\log M_n-(n+1)R}{\sqrt{n+1}}=\liminf_{n\to\infty}\frac{\log M_n-nR}{\sqrt n}$$
--   in the extended reals: assigning the sizes $M_n$ to blocklength $n+1$ instead of $n$ does not change the second-order rate at any first-order rate $R$.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 14, Lemma 7, eq. (70), with eqs. (9), (16)

import Definitions.Def_GaussianBCSecondOrder_Codes

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem equal_energy_reduction (S₁ S₂ ρ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (∀ (n M₁ M₂ : ℕ) (code : Code n M₁ M₂),
      ∃ code' : Code (n + 1) M₁ M₂,
        (∀ m₁ m₂, code'.condError S₁ S₂ ρ m₁ m₂ = code.condError S₁ S₂ ρ m₁ m₂) ∧
        (∀ m₁ m₂, ‖code'.encoder m₁ m₂‖ ^ 2 = ((n + 1 : ℕ) : ℝ))) ∧
    (∀ (M : ℕ → ℕ) (R : ℝ),
      liminf (fun n : ℕ =>
          (((Real.log (M n) - ((n + 1 : ℕ) : ℝ) * R) / Real.sqrt ((n + 1 : ℕ) : ℝ) : ℝ) : EReal))
          atTop =
        liminf (secondOrderRate M R) atTop) := by sorry
end GaussianBCSecondOrder
