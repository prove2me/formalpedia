-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_theorem_4_1
-- name    : HeavyTailNV.Tail.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:27.26808+00:00
-- url     : https://prove2.me/theorems/fa239ad8-7cd3-4d1e-818f-3c6be208e6ed
-- title:
--   Theorem 4.1 — Karamata's theorem for a tail integral
-- statement:
--   Let $u:[0,\infty)\to[0,\infty)$ be locally integrable and regularly varying with index $-\alpha$ for $\alpha>1$. Then the tail integral $U(x)=\int_x^\infty u(t)\,dt$ is finite and
--
--   $$U\in RV_{-\alpha+1},\qquad\lim_{x\to\infty}\frac{xu(x)}{U(x)}=\alpha-1.$$
--
--   The theorem relates power-law survival tails to their integrated tails and to moment finiteness.
--
--   **Formalization Note** Local integrability is explicit: the following theorem on the same page states it as its standing condition. The formal statement treats $u$ as a real function nonnegative on $[0,\infty)$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 27, Theorem 4.1

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open MeasureTheory Filter

theorem theorem_4_1 (u : ℝ → ℝ) (α : ℝ)
    (hu : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hloc : LocallyIntegrableOn u (Set.Ici 0)) (hα : 1 < α)
    (hrv : IsRegularlyVarying u (-α)) :
    (∀ x : ℝ, 0 ≤ x → IntegrableOn u (Set.Ioi x)) ∧
      IsRegularlyVarying (fun x => ∫ t in Set.Ioi x, u t) (-α + 1) ∧
      Tendsto (fun x => x * u x / ∫ t in Set.Ioi x, u t) atTop
        (nhds (α - 1)) := by sorry

end HeavyTailNV.Tail
