-- Prove2me | Theorems.Thm_HilbertSixth_hard_sphere_flow_wellposed
-- name    : HilbertSixth.hard_sphere_flow_wellposed
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:14:26.7164+00:00
-- url     : https://prove2.me/theorems/983d89d3-6e52-44a0-b28e-6f5b3c0c7e9c
-- title:
--   Proposition 1.2: the hard-sphere flow exists, is a.e. unique, and preserves Lebesgue measure
-- statement:
--   **Proposition 1.2 of arXiv:2503.01800** (proved by Alexander for the Euclidean case). Let $d \in \{2,3\}$, let $N$ be a number of particles and let $0 < \varepsilon < 1/2$ be the sphere diameter.
--
--   Up to a Lebesgue-null subset of the non-overlapping domain $\mathcal{D}_N$, the hard-sphere time evolution of Definition 1.1 exists and is unique, no two collisions occur at the same time, and the flow maps $H_N(t)$ are measure-preserving bijections of $\mathcal{D}_N$ satisfying the semigroup property $H_N(t+s) = H_N(t)H_N(s)$ for $t, s \ge 0$.
--
--   Formally: there exists a hard-sphere flow (a flow map together with the semigroup, bijectivity, measure-preservation and almost-everywhere trajectory properties) whose orbits almost surely exhibit at most one colliding pair at any time; and any two hard-sphere flows agree almost everywhere at each time $t \ge 0$.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, p. 5, Proposition 1.2 (and Definition 1.1); Deng--Hani--Ma, Long time derivation of the Boltzmann equation from hard sphere dynamics, https://arxiv.org/abs/2408.07818, p. 4, Proposition 1.2

import Definitions.Def_HilbertSixth_HardSphere

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem hard_sphere_flow_wellposed (d N : ℕ) (hd : d = 2 ∨ d = 3) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (∃ Φ : HardSphereFlow d N ε torusDist,
        ∀ᵐ z ∂(volume.restrict (domain torusDist N ε)),
          ∀ t : ℝ, 0 ≤ t → ∀ i j k l : Fin N, i ≠ j → k ≠ l →
            torusDist (Φ.H t z i).1 (Φ.H t z j).1 = ε →
            torusDist (Φ.H t z k).1 (Φ.H t z l).1 = ε →
            (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      (∀ Φ Ψ : HardSphereFlow d N ε torusDist, ∀ t : ℝ, 0 ≤ t →
        ∀ᵐ z ∂(volume.restrict (domain torusDist N ε)), Φ.H t z = Ψ.H t z) := by
  sorry

end HilbertSixth
