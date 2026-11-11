-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_2_2
-- name    : LogConcaveLattice.Lift.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:58.171331+00:00
-- url     : https://prove2.me/theorems/daa81510-ccd2-43d8-a24d-38f33206dd29
-- title:
--   Lemma 2.2 — $\Pi_E\Lambda$ is a lattice iff $E^\perp$ is a lattice subspace of $\Lambda$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice and let $E\subseteq\mathbb R^n$ be a linear subspace. The following are equivalent:
--   1. $\Pi_E\Lambda$ is a lattice in $E$, i.e. the additive subgroup $\Pi_E\Lambda\subseteq E$ is discrete;
--   2. $E^\perp$ is a lattice subspace of $\Lambda$, i.e. $\operatorname{span}_{\mathbb R}(\Lambda\cap E^\perp)=E^\perp$.
--
--   It tells exactly when a projected lattice is again a lattice, which the proof of Theorem 1.1 needs for the quotient lattice $\Pi_{E^\perp}\Lambda$ and the converse needs for $\Pi_E\Lambda$.
--
--   Differences from the source:
--   - encoding: "Π_E Λ is a lattice in E" → the image subgroup Π_E Λ ⊆ Rⁿ is discrete (DiscreteTopology); reason: a lattice is a discrete subgroup, Π_E Λ ⊆ E, and E carries the subspace topology; same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 2.2, p. 7 (citing Kannan–Lovász, Lemma 1.1)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

namespace LogConcaveLattice.Lift

/-- **Lemma 2.2** (p. 7): let `Λ ⊆ ℝⁿ` be a full-rank lattice and `E ⊆ ℝⁿ` a subspace. Then
`Π_E Λ` is a lattice in `E` (a discrete subgroup) if and only if `E⊥` is a lattice subspace
of `Λ`. -/
theorem lemma_2_2 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) :
    DiscreteTopology (projLattice E Λ) ↔ IsLatticeSubspace Λ Eᗮ := by sorry

end LogConcaveLattice.Lift
