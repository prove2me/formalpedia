-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_theorem_3_1
-- name    : OnlineRandomization.Potential.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:29:35.727639+00:00
-- url     : https://prove2.me/theorems/9acbd3cc-9709-4e17-ab87-77825244d0dc
-- title:
--   Theorem 3.1, p. 15 — an augmented potential function and an oblivious β-competitive H give a deterministic α∘β-competitive algorithm
-- statement:
--   Let a request-answer game with finite nonempty answer set $A$ and cost functions $f_n$ be given, and let $\alpha, \beta : \mathbb R \to \mathbb R$ be linear (affine) functions, $\alpha$ nondecreasing. Suppose that
--
--   1. $\Phi = \{\Phi_n\}$ is an augmented potential function for $\alpha$ and a randomized online algorithm $G$ (Definition 3.1), and
--   2. $H$ is a randomized online algorithm, a distribution over deterministic algorithms $H_y$, that is $\beta$-competitive against any oblivious adversary: $\mathbb E_y[f_n(r, H_y(r))] \le \beta(c(r))$ for every $r$.
--
--   Call a deterministic online algorithm $M = \{m_n\}$ a **potential-rule algorithm** if for every $r \in R^n$ and every $r' = r t \in R^{n+1}$,
--   $$
--   \mathbb E_y\big[\Phi_{n+1}(r', M(r)\, m_{n+1}(r'), H_y(r'))\big] \ge \mathbb E_y\big[\Phi_n(r, M(r), H_y(r))\big].
--   $$
--   Then a potential-rule algorithm exists, and every potential-rule algorithm $M$ is $\alpha \circ \beta$-competitive: for every request sequence $r$,
--   $$
--   c_M(r) \le \alpha\big(\beta(c(r))\big).
--   $$
--
--   Since $M$ is deterministic, this is also $\alpha \circ \beta$-competitiveness against adaptive off-line adversaries. The theorem is a constructive version of the paper's Corollary 2.1: it builds the deterministic algorithm explicitly, answer by answer, from a potential-function analysis of $G$ and the algorithm $H$.
--
--   **Formalization Note** The statement has two parts, existence of a potential-rule algorithm and competitiveness of every such algorithm; the second part alone would hold vacuously if no algorithm obeyed the rule. $G$ is given in behavioural form; it enters only through property 3 of $\Phi$. Costs are real-valued (the paper allows $+\infty$). Monotonicity of $\alpha$ is added: the paper only says "linear", but the last step of its proof applies $\alpha$ to the inequality $\mathbb E_y[f_n(r, H_y(r))] \le \beta(c(r))$, which needs $\alpha$ nondecreasing (the paper's examples are ratios $d > 0$). The page's "$k_1, k_2, \dots, m_n$" is read as $m_1, \dots, m_n$. The expectations over $y$ are Bochner integrals.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 15, Theorem 3.1 (proof pp. 15-16)

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

theorem theorem_3_1 {R A Ω : Type*} [Fintype A] [Nonempty A] [MeasurableSpace Ω]
    (F : Game R A) (α β : ℝ → ℝ) (hα : IsLinear α) (hα_mono : Monotone α)
    (hβ : IsLinear β) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (hH : IsCompetitiveObl F β H) :
    (∃ M : DetAlg R A, ObeysPotentialRule Φ H M) ∧
      ∀ M : DetAlg R A, ObeysPotentialRule Φ H M → IsCompetitive F (α ∘ β) M := by sorry

end OnlineRandomization.Potential
