-- Prove2me | Theorems.Thm_MondererShapley_Improvement_exists_represent
-- name    : MondererShapley.Improvement.exists_represent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:46.37315+00:00
-- url     : https://prove2.me/theorems/f46f2786-b7b8-4dd9-916e-b9b44db4fc95
-- title:
--   Lemma 2.5, proof — the full profile set is represented
-- statement:
--   Let $\Gamma$ be a finite game with the FIP, and let $x>y$ mean that a finite strict improvement path leads from $y$ to a distinct profile $x$. Then the whole profile set $Y$ is **represented**: there is a function $Q:Y\to\mathbb R$ such that
--
--   $$
--   x>y\quad\Longrightarrow\quad Q(x)>Q(y)\qquad(x,y\in Y).
--   $$
--
--   This is the conclusion of the maximal-represented-subset argument in the proof of Lemma 2.5. It provides an order-respecting real function on every profile.
--
--   **Formalization Note** The inequality is written `Q y < Q x` because the Lean relation `ImprovesTo u x y` names the destination first.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 129–130 (PDF pp. 6–7), Lemma 2.5 proof, “Hence Y is represented”

import Mathlib
import Definitions.Def_MondererShapley_Improvement_ImprovesTo
import Definitions.Def_MondererShapley_Improvement_HasFIP

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- The conclusion `Y is represented` in the proof of Lemma 2.5 (pp. 129–130). -/
theorem exists_represent [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (hFIP : HasFIP u) :
    ∃ Q : (∀ i, Y i) → ℝ,
      ∀ x y, ImprovesTo u x y → Q y < Q x := by sorry

end MondererShapley.Improvement
