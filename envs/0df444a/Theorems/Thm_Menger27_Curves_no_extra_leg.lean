-- Prove2me | Theorems.Thm_Menger27_Curves_no_extra_leg
-- name    : Menger27.Curves.no_extra_leg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:36.774843+00:00
-- url     : https://prove2.me/theorems/2d4f9286-bc3f-4b33-9962-8455f4bb0678
-- title:
--   pp. 97–98 — order at most n excludes an (n+1)-leg
-- statement:
--   Let $p$ be a point of a metric space with order at most $n$. Then no collection of $n+1$ arcs can end at $p$ and be pairwise disjoint away from $p$:
--   $$\neg\operatorname{HasNBein}(p,n+1).$$
--
--   This is the upper-bound half of the order characterization. **Formalization Note** The paper states it for a point of exact order $n$; the same observation uses only order at most $n$. No regular-curve assumption is needed.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 97–98, sentence beginning “Mehr als n” on p. 97 and continuing on p. 98

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- The observation spanning pp. 97–98: order at most `n` excludes `n+1` legs. -/
theorem no_extra_leg {X : Type*} [MetricSpace X]
    (p : X) (n : ℕ) (horder : OrderAtMost p n) :
    ¬ HasNBein p (n + 1) := by sorry

end Menger27.Curves
