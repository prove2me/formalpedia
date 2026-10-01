-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_fundamental_matrix_relations
-- name    : JewellMRP.InfiniteStep.fundamental_matrix_relations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:31:28.253464+00:00
-- url     : https://prove2.me/theorems/3fbf567b-8a98-4ab8-b248-2b67e89920eb
-- title:
--   Appendix A, p. 966 — $Z = [I-(P-\Pi)]^{-1}$ exists and satisfies $PZ = ZP$, $\pi Z = \pi$, $I - Z = \Pi - PZ$
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set, $\pi$ its stationary probability vector, and $\Pi$ the matrix all of whose rows equal $\pi$. Then the matrix $I - (P - \Pi)$ is invertible, and its inverse, the fundamental matrix $Z = (I - P + \Pi)^{-1}$, satisfies
--   $$PZ = ZP, \qquad \pi Z = \pi, \qquad I - Z = \Pi - PZ .$$
--
--   These are the algebraic relations of the Kemeny–Snell fundamental matrix that Appendix A uses to identify the limiting bias vector.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 966, Appendix A (before Eq. (A 4)); p. 952, Eq. (A 7)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem fundamental_matrix_relations {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π) :
    IsUnit (1 - (P - limitMatrix π)) ∧
      P * fundamentalMatrix P π = fundamentalMatrix P π * P ∧
      π ᵥ* fundamentalMatrix P π = π ∧
      1 - fundamentalMatrix P π = limitMatrix π - P * fundamentalMatrix P π := by sorry

end JewellMRP.InfiniteStep
