-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_scale
-- name    : IgnallSchrage.Invariance.scale
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:48.025991+00:00
-- url     : https://prove2.me/theorems/99f6f87b-605e-4bf8-967a-fc1971660c09
-- title:
--   p. 411 — multiplying all processing times by $H>0$ multiplies objectives and lower bounds by $H$
-- statement:
--   Let $H>0$ and multiply every processing time by $H$. Then, for arbitrary real processing times,
--
--   1. the three-machine makespan of every full sequence is multiplied by $H$;
--   2. the two-machine sum of completion times $\sum_i d_i$ of every full sequence is multiplied by $H$;
--   3. the three-machine lower bound $LB(J_r)$ of every node is multiplied by $H$;
--   4. on two machines, $\hat T_r$, $\hat S_r$ and $LB(J_r)$ of every node are multiplied by $H$.
--
--   The paper argues by a change of time units: "Define new time units so that when $\tilde a_i,\tilde b_i,\tilde c_i$ are measured in these units, and $a'_i,b'_i,c'_i$ in their original units, $H$ will be $1$." The mathematical content of that step is that all these quantities are positively homogeneous of degree one in the processing times, which is what is stated here.
--
--   **Formalization Note** No sign condition is needed for scaling. The identities hold at every node, the root included, since $H\cdot 0=0$ for the placeholder minima.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (Now suppose H≠1. Define new time units …)

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- p. 411 ("Define new time units"): multiplying all processing times by `H > 0` multiplies the
makespan and the sum of completion times of every sequence, and `T̂_r`, `Ŝ_r`, both lower
bounds of every node, by `H`. -/
theorem scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) :
    (∀ σ : Equiv.Perm (Fin n),
      IgnallSchrage.Makespan.makespan (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) σ =
        H * IgnallSchrage.Makespan.makespan a b c σ) ∧
    (∀ σ : Equiv.Perm (Fin n),
      sumCompletion (fun i => H * a i) (fun i => H * b i) σ = H * sumCompletion a b σ) ∧
    (∀ J : List (Fin n),
      lowerBound3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) J =
        H * lowerBound3 a b c J) ∧
    (∀ J : List (Fin n),
      That (fun i => H * a i) (fun i => H * b i) J = H * That a b J ∧
      Shat (fun i => H * a i) (fun i => H * b i) J = H * Shat a b J ∧
      lowerBound2 (fun i => H * a i) (fun i => H * b i) J = H * lowerBound2 a b J) := by sorry

end IgnallSchrage.Invariance
