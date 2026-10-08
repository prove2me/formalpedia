-- Prove2me | Theorems.Thm_MondererShapley_Improvement_improvesTo_trans
-- name    : MondererShapley.Improvement.improvesTo_trans
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:57.40204+00:00
-- url     : https://prove2.me/theorems/88708de7-ddeb-4c34-919e-a087f6b2db8c
-- title:
--   Lemma 2.5, proof — transitivity of improvement reachability
-- statement:
--   Let $\Gamma$ have the FIP and write $x>y$ when a finite strict improvement path leads from $y$ to a distinct profile $x$. Then this relation is transitive:
--
--   $$
--   x>y\ \land\ y>z\quad\Longrightarrow\quad x>z.
--   $$
--
--   This is the intermediate claim stated in the proof of Lemma 2.5. The FIP is essential because a closed strict improvement walk would violate it.
--
--   **Formalization Note** Strategy sets may be infinite here; the paper says only “a game with the FIP” at this point.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 129 (PDF p. 6), Lemma 2.5 proof, “>” is transitive

import Mathlib
import Definitions.Def_MondererShapley_Improvement_ImprovesTo
import Definitions.Def_MondererShapley_Improvement_HasFIP

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- In the proof of Lemma 2.5 (p. 129), the FIP makes `>` transitive. -/
theorem improvesTo_trans [Fintype ι] (u : ι → (∀ i, Y i) → ℝ)
    (hFIP : HasFIP u) (x y z : ∀ i, Y i)
    (hxy : ImprovesTo u x y) (hyz : ImprovesTo u y z) :
    ImprovesTo u x z := by sorry

end MondererShapley.Improvement
