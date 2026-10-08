-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_competitive_against_H
-- name    : OnlineRandomization.Potential.competitive_against_H
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:29:15.95001+00:00
-- url     : https://prove2.me/theorems/b2a1dae9-e608-409f-bd33-4c03fb62f9ac
-- title:
--   Proof of Theorem 3.1, p. 15 — M is α-competitive against the randomized adaptive on-line adversary S = (Q, H)
-- statement:
--   Let $\alpha$ be linear, $\alpha(x) = c x + d$, let $\Phi$ be an augmented potential function for $\alpha$ and a randomized online algorithm $G$ (Definition 3.1), let $H$ be a randomized online algorithm given as a distribution over deterministic algorithms $H_y$, and let $M$ be a deterministic online algorithm that obeys the potential rule of Theorem 3.1 for $\Phi$ and $H$. Then for every request sequence $r \in R^n$,
--   $$
--   f_n(r, M(r)) \le \mathbb E_y\big[\alpha\big(f_n(r, H_y(r))\big)\big].
--   $$
--
--   In the paper's words, $M$ is $\alpha$-competitive against the randomized adaptive on-line adversary $S = (Q, H)$ that asks $r$ and serves it with $H$: the cost of $M$ is $c_M(S) = f_n(r, M(r))$ and the adversary's cost is $c_S(M) = f_n(r, H_y(r))$. It is the step that, combined with the $\beta$-competitiveness of $H$, gives Theorem 3.1.
--
--   **Formalization Note** $\alpha$ stays inside the expectation, as in the paper's definition of competitiveness against adaptive adversaries (p. 9). Linearity of $\alpha$ is the paper's standing convention (p. 7) and is kept as a hypothesis. The expectation over $y$ is a Bochner integral; costs are real-valued (the paper allows $+\infty$).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 15, §3, proof of Theorem 3.1, last paragraph, second claim

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

open MeasureTheory

theorem competitive_against_H {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (hα : IsLinear α) (g : BehAlg R A)
    (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω)
    (M : DetAlg R A) (hM : ObeysPotentialRule Φ H M) (r : List R) :
    M.costOn F r ≤ ∫ y, α ((H.alg y).costOn F r) ∂H.μ := by sorry

end OnlineRandomization.Potential
