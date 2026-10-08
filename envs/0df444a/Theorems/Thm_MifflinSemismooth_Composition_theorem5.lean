-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_theorem5
-- name    : MifflinSemismooth.Composition.theorem5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:22.734071+00:00
-- url     : https://prove2.me/theorems/3ae915ea-fd15-45cc-a239-b3fef328bf95
-- title:
--   Theorem 5 — semismooth composition of semismooth functions
-- statement:
--   Let every component $f_i:\mathbb R^n\to\mathbb R$ and the outer function $E:\mathbb R^m\to\mathbb R$ be Lipschitz on bounded sets, as in Theorem 4. If every $f_i$ is semismooth at $x$ and $E$ is semismooth at $Y(x)=(f_1(x),\ldots,f_m(x))$, then
--
--   $$F=E\circ Y\quad\text{is semismooth at }x. $$
--
--   The theorem gives closure of the paper's pointwise semismoothness under a semismooth outer composition.
--
--   **Formalization Note** Semismoothness is Definition 1's condition on the accumulation points of generalized-gradient pairings. The conclusion is at the specified point $x$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 14, Theorem 5

import Mathlib
import Definitions.Def_MifflinSemismooth_Composition_Setting
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded

namespace MifflinSemismooth.Composition

theorem theorem5 {n m : ℕ}
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ∀ i, ClarkeGradients.Shared.LipschitzOnBounded (f i))
    (hE : ClarkeGradients.Shared.LipschitzOnBounded E)
    (x : EuclideanSpace ℝ (Fin n))
    (hfs : ∀ i, MifflinSemismooth.Extremal.SemismoothAt (f i) x)
    (hEs : MifflinSemismooth.Extremal.SemismoothAt E (Y f x)) :
    MifflinSemismooth.Extremal.SemismoothAt (compF E f) x := by sorry

end MifflinSemismooth.Composition
