-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_theorem_4_2_b
-- name    : HeavyTailNV.Tail.theorem_4_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:12.520258+00:00
-- url     : https://prove2.me/theorems/c4f804df-7667-4671-a942-d63ae9cd3c5a
-- title:
--   Theorem 4.2(b) — monotone density converse
-- statement:
--   Let $u$ be a nonnegative, locally integrable, monotone function on $[0,\infty)$, and define the tail integral $U(x)=\int_x^\infty u(t)\,dt$. If $U\in RV_{-\alpha}$ with $\alpha>0$, then
--
--   $$\lim_{x\to\infty}\frac{xu(x)}{U(x)}=\alpha,\qquad u\in RV_{-\alpha-1}.$$
--
--   This converse transfers the shortage tail's index to the demand survival tail.
--
--   **Formalization Note** Display (4.4) prints $-\alpha$ for the positive ratio; the corrected sign is $+\alpha$. The regularly varying tail integral is eventually positive; with nonnegative $u$, this excludes a nonintegrable tail being assigned a default zero Bochner integral.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 27, Theorem 4.2(b), (4.4)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open MeasureTheory Filter

theorem theorem_4_2_b (u : ℝ → ℝ) (α : ℝ)
    (hu : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hloc : LocallyIntegrableOn u (Set.Ici 0))
    (hα : 0 < α)
    (hU : IsRegularlyVarying (fun x => ∫ t in Set.Ioi x, u t) (-α))
    (hmono : MonotoneOn u (Set.Ici 0) ∨ AntitoneOn u (Set.Ici 0)) :
    Tendsto (fun x => x * u x / ∫ t in Set.Ioi x, u t) atTop (nhds α) ∧
      IsRegularlyVarying u (-α - 1) := by sorry

end HeavyTailNV.Tail
