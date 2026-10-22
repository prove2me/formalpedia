-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_eq_2_15
-- name    : ImpulseNMFG.Verification.eq_2_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:30.45546+00:00
-- url     : https://prove2.me/theorems/57a5a211-2e15-418a-9e78-ad80c9216878
-- title:
--   Theorem 2.12, proof, (2.15a)–(2.15c), p. 10 — candidate opponents wait and act at equality
-- statement:
--   Fix player $i$ and an admissible unilateral deviation while every other player follows the candidate profile. For each opponent $j\ne i$, the controlled state lies in $D_j$ at positive times before exit that are not intervention instants. At the $k$th intervention of player $j$ before exit, the own intervention gap vanishes and the impulse is the prescribed $\xi_j$:
--   $$
--   (\mathcal M_jV_j-V_j)(X_s)>0,\qquad
--   (\mathcal M_jV_j-V_j)(X_{(\tau_{j,k})-})=0,\qquad
--   \xi_{j,k}=\xi_j(X_{(\tau_{j,k})-}).
--   $$
--   This is the region and intervention information used to apply the QVI to a deviating profile.
--
--   **Formalization Note** The first assertion is restricted to $0<s<\tau_S$ away from intervention instants, as required by Lemma 2.3 and the next page of the proof. The other assertions require $\tau_{j,k}<\tau_S$. The deviation and its realization are admissible.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, p. 10, Theorem 2.12, proof, (2.15a)–(2.15c)

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State)

namespace ImpulseNMFG.Verification
noncomputable section

/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, p. 10, Theorem 2.12, proof, (2.15a)–(2.15c).
Against the candidate opponents, their strict waiting inequalities hold between
interventions, and each opponent acts at equality with the prescribed impulse.
The displayed (2.15a) is restricted to positive non-intervention times before exit,
as the next page and Lemma 2.3 require. -/
theorem eq_2_15 {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (G : Game N d M) (V : Fin N → State d → ℝ)
    (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (x : State d) (hx : x ∈ G.S) (i : Fin N)
    (A : Set (State d)) (ξ' : State d → G.Imp i)
    (Y : ℕ → ℝ≥0 → Ω → State d)
    (hY : IsAdmissible P 𝔽 W G x ((starProfile G V ξ).update i A ξ') Y) :
    ∀ ω, ∀ j : Fin N, j ≠ i →
      (∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) <
          exitTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
          (s : ℝ≥0∞) ∉
            interventionTimes G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
          0 < ownOp G V ξ j
            (ctrl G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) s) -
            V j (ctrl G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) s)) ∧
      (∀ n : ℕ, 1 ≤ n →
        interTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n <
          exitTime G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) →
        ownOp G V ξ j
          (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n) -
          V j (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n) = 0 ∧
        impulse G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n =
          ξ j (preState G x ((starProfile G V ξ).update i A ξ') (pathOf Y ω) j n)) := by sorry

end
end ImpulseNMFG.Verification
