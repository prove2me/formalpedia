-- Prove2me | Theorems.Thm_NoHair_rest_frame_exists
-- name    : NoHair.rest_frame_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T01:40:51.694284+00:00
-- url     : https://prove2.me/theorems/281d87a2-2fb3-49fb-ac45-8cb3c57f5a2e
-- title:
--   Changing the reference frame I: boosting to the rest frame
-- statement:
--   Let $P\in\mathbb R^4$ be a future-directed timelike 4-momentum: $\eta(P,P)=P^{\mathsf T}\eta P<0$ and $P^0>0$, with $\eta=\mathrm{diag}(-1,1,1,1)$. Then there is a proper orthochronous Lorentz transformation $\Lambda$ ($\Lambda^{\mathsf T}\eta\Lambda=\eta$, $\det\Lambda=1$, $\Lambda^0{}_0\ge1$) with
--   $$\Lambda P=\big(\sqrt{-\eta(P,P)},0,0,0\big).$$
--
--   This is the step of the source's frame argument that sets the linear momentum to zero.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone (changing the reference frame I): rest frame.** Every future-directed timelike
4-momentum `P` is carried by a proper orthochronous Lorentz transformation to
`(√(-η(P,P)), 0, 0, 0)`. -/
theorem rest_frame_exists (P : Fin 4 → ℝ) (hP : P ⬝ᵥ (minkowski *ᵥ P) < 0) (hP0 : 0 < P 0) :
    ∃ Λ : Matrix (Fin 4) (Fin 4) ℝ, Λᵀ * minkowski * Λ = minkowski ∧ Λ.det = 1 ∧
      1 ≤ Λ 0 0 ∧ Λ *ᵥ P = ![Real.sqrt (-(P ⬝ᵥ (minkowski *ᵥ P))), 0, 0, 0] := by
  sorry

end NoHair
