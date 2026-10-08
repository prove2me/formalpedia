-- Prove2me | Theorems.Thm_OnlineRandomization_Potential_potential_invariant
-- name    : OnlineRandomization.Potential.potential_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:29:18.837994+00:00
-- url     : https://prove2.me/theorems/02052ca9-3eeb-47fe-8e32-f485a6ad9cf6
-- title:
--   Proof of Theorem 3.1, p. 15 — along the rule, E_y[Φ_n(r, M(r), H_y(r))] ≥ 0 for every r
-- statement:
--   Let $\Phi$ be an augmented potential function for a function $\alpha$ and a randomized online algorithm $G$ (Definition 3.1), let $H$ be a randomized online algorithm given as a distribution over deterministic algorithms $H_y$, and let $M$ be a deterministic online algorithm that obeys the potential rule of Theorem 3.1 for $\Phi$ and $H$. Then for every $n$ and every $r \in R^n$,
--   $$
--   \mathbb E_y\big[\Phi_n(r, M(r), H_y(r))\big] \ge 0 .
--   $$
--
--   This invariant is what makes the rule work: by property 2 of Definition 3.1 it converts into a bound on the cost of $M$.
--
--   **Formalization Note** The expectation over $y$ is a Bochner integral under $H$'s probability measure. The page's "$H_y r))$" is read as $H_y(r)$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 15, §3, proof of Theorem 3.1, last paragraph, first claim

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

namespace OnlineRandomization.Potential

open MeasureTheory

theorem potential_invariant {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (M : DetAlg R A)
    (hM : ObeysPotentialRule Φ H M) (r : List R) :
    0 ≤ ∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ := by sorry

end OnlineRandomization.Potential
