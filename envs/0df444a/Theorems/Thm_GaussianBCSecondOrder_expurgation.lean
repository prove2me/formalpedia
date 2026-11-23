-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_expurgation
-- name    : GaussianBCSecondOrder.expurgation
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:31:38.575181+00:00
-- url     : https://prove2.me/theorems/8cd33f02-b57a-46a0-b8e3-9d8a4400feb2
-- title:
--   Lemma 6: expurgation with cloud-center-dependent relabeling
-- statement:
--   This lemma converts a code with small augmented average error probability into a code with small maximal error probability, at a constant-factor loss in the message sizes.
--
--   Let $S_1>S_2>0$, $\rho\in[-1,1]$ and $\varepsilon\in(0,1)$.
--
--   **Lemma.** Let an $(n,M_{1,n},M_{2,n})$-code in which receiver 1 estimates both messages have augmented average error probability at most $\varepsilon+\xi/2$, where $\xi\in(0,1-\varepsilon)$, and put $\theta=\xi/[2(\varepsilon+\xi)]$. By selecting cloud centers (values of $m_2$) and satellite codewords (values of $m_1$ within each selected center) and relabeling the retained satellites separately within each selected center, one obtains a code with
--   $$M_{j,n}'=\Big\lceil\frac{\theta M_{j,n}}2\Big\rceil,\quad j=1,2,\qquad\text{and}\qquad\varepsilon_{n,\max}'\le\varepsilon+\xi .$$
--   The new code is a subcode of the original one and therefore satisfies the original power constraint.
--
--   Together with Proposition 5 this yields achievability of the regions of Theorem 1 under the maximal error criterion.
--
--   **Formalization Note** The parameter assumptions of Theorem 1 are hypotheses. "Selecting and relabeling" is expressed by an injective map $g_2$ from new to old receiver-2 messages and, for each new receiver-2 message $m_2$, an injective map $g_1(m_2,\cdot)$ from new to old receiver-1 messages, such that the new codeword of $(m_1,m_2)$ is the old codeword of $(g_1(m_2,m_1),g_2(m_2))$. The power constraint is part of the definition of a code. The new maximal error probability is the ordinary (not augmented) one.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 13, Lemma 6, eq. (69)

import Definitions.Def_GaussianBCSecondOrder_Superposition

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem expurgation (S₁ S₂ ρ ε ξ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hξ : ξ ∈ Set.Ioo 0 (1 - ε))
    (n M₁ M₂ : ℕ) (code : AugCode n M₁ M₂)
    (herr : code.augAvgError S₁ S₂ ρ ≤ ε + ξ / 2) :
    ∃ code' : Code n ⌈ξ / (2 * (ε + ξ)) * M₁ / 2⌉₊ ⌈ξ / (2 * (ε + ξ)) * M₂ / 2⌉₊,
      (∀ m₁ m₂, code'.condError S₁ S₂ ρ m₁ m₂ ≤ ε + ξ) ∧
      ∃ (g₂ : Fin ⌈ξ / (2 * (ε + ξ)) * M₂ / 2⌉₊ → Fin M₂)
        (g₁ : Fin ⌈ξ / (2 * (ε + ξ)) * M₂ / 2⌉₊ → Fin ⌈ξ / (2 * (ε + ξ)) * M₁ / 2⌉₊ → Fin M₁),
        Function.Injective g₂ ∧ (∀ m₂, Function.Injective (g₁ m₂)) ∧
        ∀ m₁ m₂, code'.encoder m₁ m₂ = code.encoder (g₁ m₂ m₁) (g₂ m₂) := by sorry
end GaussianBCSecondOrder
