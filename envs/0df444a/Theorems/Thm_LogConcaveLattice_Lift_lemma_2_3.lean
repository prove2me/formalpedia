-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_2_3
-- name    : LogConcaveLattice.Lift.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:58.724469+00:00
-- url     : https://prove2.me/theorems/f612b689-1f0c-4c1f-bfad-63d54d1ef422
-- title:
--   Lemma 2.3 — $\det\Lambda=\det(\Lambda\cap E)\det(\Pi_{E^\perp}\Lambda)$ and $(\Pi_{E^\perp}\Lambda)^*=\Lambda^*\cap E^\perp$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice and let $E\subseteq\mathbb R^n$ be a lattice subspace of $\Lambda$ ($\operatorname{span}_{\mathbb R}(\Lambda\cap E)=E$). Then
--   1. $\det\Lambda=\det(\Lambda\cap E)\cdot\det(\Pi_{E^\perp}\Lambda)$;
--   2. $(\Pi_{E^\perp}\Lambda)^*=\Lambda^*\cap E^\perp$;
--   3. in particular, $E^\perp$ is a lattice subspace of $\Lambda^*$.
--
--   Here $\det(\Lambda\cap E)$ and $\det(\Pi_{E^\perp}\Lambda)$ are determinants of lower-rank lattices computed in their spans, and the dual of $\Pi_{E^\perp}\Lambda$ is taken inside its span $E^\perp$.
--
--   The lemma drives the induction on dimension in the proof of Theorem 1.1 (weak stability passes from $\Lambda^*$ to $(\Pi_{E^\perp}\Lambda)^*$, and the periodization constants multiply) and the duality step of the converse.
--
--   Differences from the source:
--   - encoding: det Λ (full rank) → ZLattice.covolume Λ; determinants of the lower-rank lattices Λ ∩ E and Π_{E⊥}Λ → Gram determinants of lattice bases; reason: the determinant computed in the span (p. 7); same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 2.3, p. 7 (citing Regev–Stephens-Davidowitz, Section 2)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

namespace LogConcaveLattice.Lift

/-- **Lemma 2.3** (p. 7): let `Λ ⊆ ℝⁿ` be a full-rank lattice and `E` a lattice subspace of
`Λ`. Then `det Λ = det(Λ ∩ E) · det(Π_{E⊥} Λ)`; moreover `(Π_{E⊥} Λ)* = Λ* ∩ E⊥`; in particular
`E⊥` is a lattice subspace of `Λ*`. -/
theorem lemma_2_3 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) (hE : IsLatticeSubspace Λ E) :
    ZLattice.covolume Λ = latticeDet (interSubspace Λ E) * latticeDet (projLattice Eᗮ Λ) ∧
      dual (projLattice Eᗮ Λ) = interSubspace (dual Λ) Eᗮ ∧
      IsLatticeSubspace (dual Λ) Eᗮ := by sorry

end LogConcaveLattice.Lift
