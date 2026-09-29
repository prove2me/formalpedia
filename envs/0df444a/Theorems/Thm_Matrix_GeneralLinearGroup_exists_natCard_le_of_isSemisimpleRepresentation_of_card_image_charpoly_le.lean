-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
-- name    : Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/94a9209a-fad6-56df-98de-75026634c8ba
-- title:
--   Deligne–Serre: uniform bound for few characteristic polynomials
-- statement:
--   Let $\eta$ be a real number with $\eta < 1/2$ and let $M$ be a natural number. The assertion is that there exists a natural number $A$ with the following property, uniform in the prime and in the group: for every prime $\ell$ and every subgroup $G \le \mathrm{GL}_2(\mathbb{Z}/\ell)$ such that the representation of $G$ on $\mathbb{Z}/\ell$-column vectors $\mathrm{Fin}\,2 \to \mathbb{Z}/\ell$ obtained from the inclusion $G \hookrightarrow \mathrm{GL}_2(\mathbb{Z}/\ell)$ (the tautological two-dimensional representation, here the composite of `G.subtype` with the identification of invertible matrices with linear automorphisms) is semisimple, and for every finite set $H$ of elements of $\mathrm{GL}_2(\mathbb{Z}/\ell)$ with $H \subseteq G$ as sets, if $(1-\eta)\,|G| \le |H|$ as real numbers, where $|G|$ denotes `Nat.card G`, and if the set of characteristic polynomials $\det(X - h)$ of the underlying matrices of the elements $h \in H$ has at most $M$ members, then $|G| \le A$. No lower bound on $\eta$ is imposed, and $A$ depends only on $\eta$ and $M$.
--
--   This is Proposition 7.2 of Deligne–Serre, the uniform bound attached to their condition $C(\eta, M)$: a semisimple subgroup of $\mathrm{GL}_2(\mathbb{F}_\ell)$ in which a proportion $1-\eta$ of the elements realises at most $M$ characteristic polynomials has order bounded independently of $\ell$. It is used in [`DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le`](thm.html#DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le), where the characteristic polynomials of Frobenius elements of a two-dimensional mod $\ell$ representation take few values on a set of primes of large density, and the conclusion is that the image of the representation has bounded order; the proof cites [`ModularCurve.SerreImage.contains_SL2`](thm.html#ModularCurve.SerreImage.contains_SL2), which produces $\mathrm{SL}_2(\mathbb{F}_\ell)$ inside a subgroup containing a nontrivial unipotent element and acting without stable lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (G : Subgroup (GL (Fin 2) (ZMod ℓ))),
      (Deformation.matrixRepresentation G.subtype).IsSemisimpleRepresentation →
      ∀ H : Finset (GL (Fin 2) (ZMod ℓ)), (↑H : Set (GL (Fin 2) (ZMod ℓ))) ⊆ G →
        (1 - η) * (Nat.card G : ℝ) ≤ H.card →
        (H.image fun h : GL (Fin 2) (ZMod ℓ) =>
            (h : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly).card ≤ M →
          Nat.card G ≤ A := by sorry
