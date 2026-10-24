-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_5
-- name    : MICPRep.Periodic.lemma_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:11.597+00:00
-- url     : https://prove2.me/theorems/51693349-451e-4de5-aa59-7023f6aeb3f4
-- title:
--   Lemma 6.5, p. 25 — flatness dichotomy: an integer point in relint(I_ℤ), or after a lattice-preserving rational map I_ℤ lies in a slab l ≤ z₁ ≤ u
-- statement:
--   Let $I \subseteq \mathbb R^d$ be a (not necessarily full-dimensional) convex set with $I \cap \mathbb Z^d \neq \emptyset$. Then either $I_{\mathbb Z}$ has an integer point in its relative interior, or there are an invertible rational affine map $R : \mathbb R^d \to \mathbb R^d$ with $R(\mathbb Z^d) = R^{-1}(\mathbb Z^d) = \mathbb Z^d$ and integers $l, u$ such that
--   $$R(I)_{\mathbb Z} \subseteq \{z \in \mathbb R^d : l \le z_1 \le u\}, \qquad \mathrm{aff}_{\mathbb Z}(R(I)) = \mathbb R^{\dim(I_{\mathbb Z})} \times \{0\}^{d - \dim(I_{\mathbb Z})}.$$
--
--   It is a variant of Khintchine's flatness theorem and drives the induction on dimension in the proof of Lemma 6.1.
--
--   **Formalization Note** $\dim(I_{\mathbb Z})$ is the integer-valued dimension of $\mathrm{aff}(I_{\mathbb Z})$; the relative interior is Mathlib's `intrinsicInterior`. $z_1$ is the coordinate with $0$-based index $0$; for $d = 0$ the slab is all of $\mathbb R^0$, and the first alternative holds anyway.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 25, Lemma 6.5

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.5, p. 25. -/
theorem lemma_6_5 {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty ∨
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ∃ l u : ℤ, IZ (ratAff A b '' I) ⊆ slab d l u ∧
        (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) = coordSubspace d (setDim (IZ I)) := by sorry

end MICPRep.Periodic
