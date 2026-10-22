-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_exists_unique_unit
-- name    : InvariantSDP.BlockDiag.exists_unique_unit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:29.103176+00:00
-- url     : https://prove2.me/theorems/7b53877e-5d37-4da4-880d-127f39d18fff
-- title:
--   p. 13 — every matrix ∗-algebra has a unique unit
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a matrix ∗-algebra. There is a unique element $E \in \mathcal A$ such that
--   $$EX = XE = X \qquad \text{for every } X \in \mathcal A,$$
--   called the unit of $\mathcal A$.
--
--   The unit need not be the identity matrix: it is the orthogonal projection onto the part of $\mathbb C^n$ on which $\mathcal A$ acts, and for $\mathcal A = \{0\}$ it is $0$. It enters the definition of a simple matrix ∗-algebra. The paper states the claim on p. 13 and shows it on p. 14 ("(ii) shows that $I_1 + \dots + I_k$ is the unit of $\mathcal A$").
--
--   **Formalization Note** $\mathcal A$ is a `NonUnitalStarSubalgebra`; no nonzero or unital hypothesis is made.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 13, terminology after Theorem 2.7 (shown in the proof of Theorem 2.7, p. 14)

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- p. 13: a matrix ∗-algebra `𝒜` has a unique element `E ∈ 𝒜` with `EX = XE = X` for every `X ∈ 𝒜`. -/
theorem exists_unique_unit {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃! E : Matrix (Fin n) (Fin n) ℂ, IsUnitOf A E := by sorry

end InvariantSDP.BlockDiag
