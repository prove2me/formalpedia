-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_11_rank
-- name    : ManipPotential.proposition_6_11_rank
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:56.481803+00:00
-- url     : https://prove2.me/theorems/32bc6ca4-c0de-41bf-9417-a1d043b0c577
-- title:
--   Proposition 6.11 — rank of the Jacobian
-- statement:
--   Let $G=(G_x,G_\tau)$ be differentiable at a point of an open set $U$ on which its external coordinates are the identity and its total cyclic coordinate is $\tau$. Then its Fréchet derivative is injective, and the rank of its Jacobian is
--   $$
--   \operatorname{rank}(D(G_x,G_\tau))=|C|!-|C|+1.
--   $$
--   Indeed, choose a cyclic ranking whose first two entries differ from those of the external ranking $s$. After a translation the derivative of $G_x$ in that cyclic coordinate is zero, while differentiation of the prescribed external coordinate $s$ shows that every external component of the derivative is determined by the corresponding external infinitesimal input; the derivative of $G_\tau$ similarly kills the last input. This gives injectivity and hence the rank formula.
-- source:
--   Berker–Conitzer–Hartman–Liu–Oesterheld, How Many Votes Is a Lie Worth?, arXiv:2602.22838 (v3, 2026-11-03), final paragraph of the proof of Proposition 6.11, p.35.

import Mathlib
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal

namespace ManipPotential

/-- Proposition 6.11, rank of the Jacobian, p.35. -/
theorem proposition_6_11_rank {m : ℕ} [NeZero m]
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hU : IsOpen U)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (hG : ∀ z ∈ U, (∀ s : ExtRanking m, G z s.1 = z.1 s) ∧ cycTotal (G z) = z.2) :
    ∀ z ∈ U, DifferentiableAt ℝ G z →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G z).toLinearMap) = m.factorial - m + 1 := by sorry
