-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_3
-- name    : MICPRep.Periodic.lemma_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:07.424753+00:00
-- url     : https://prove2.me/theorems/41cdd191-f0c5-4f69-8695-36ad8213ec87
-- title:
--   Lemma 6.3, p. 24 — aff_ℤ(I) is a rational affine subspace, I_ℤ keeps the integer points of I, and lattice-preserving rational maps commute with aff_ℤ and (·)_ℤ
-- statement:
--   Let $I \subseteq \mathbb R^d$ be convex with $I \cap \mathbb Z^d \ne \emptyset$. Then
--
--   1. $\mathrm{aff}_{\mathbb Z}(I)$ is a rational affine subspace;
--   2. $I_{\mathbb Z} \cap \mathbb Z^d = I \cap \mathbb Z^d$;
--   3. $\mathrm{aff}_{\mathbb Z}(I_{\mathbb Z}) = \mathrm{aff}_{\mathbb Z}(I) = \mathrm{aff}(I_{\mathbb Z})$;
--   4. if $R(z) = Az + b$ is an invertible rational affine map with $R(\mathbb Z^d) = R^{-1}(\mathbb Z^d) = \mathbb Z^d$, then
--   $$R(I_{\mathbb Z}) = R(I)_{\mathbb Z}, \qquad R(\mathrm{aff}_{\mathbb Z}(I)) = \mathrm{aff}_{\mathbb Z}(R(I)).$$
--
--   The lemma lets the proof of Lemma 6.1 replace an index set by its rational part and change integer coordinates without losing integer points.
--
--   **Formalization Note** A rational affine subspace is a nonempty affine subspace spanned by its rational points. $R$ is `ratAff A b` with $A \in \mathbb Q^{d\times d}$ invertible; $R^{-1}(\mathbb Z^d)$, the image of $\mathbb Z^d$ under $R^{-1}$, is written as the preimage of $\mathbb Z^d$ under $R$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 24, Lemma 6.3

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.3, p. 24. -/
theorem lemma_6_3 {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    IsRationalAffineSubspace (affZ I) ∧
    IZ I ∩ intLattice d = I ∩ intLattice d ∧
    affZ (IZ I) = affZ I ∧ affZ I = affineSpan ℝ (IZ I) ∧
    ∀ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A →
      ratAff A b '' intLattice d = intLattice d →
      ratAff A b ⁻¹' intLattice d = intLattice d →
      ratAff A b '' IZ I = IZ (ratAff A b '' I) ∧
      ratAff A b '' (affZ I : Set (Fin d → ℝ)) = (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) := by sorry

end MICPRep.Periodic
