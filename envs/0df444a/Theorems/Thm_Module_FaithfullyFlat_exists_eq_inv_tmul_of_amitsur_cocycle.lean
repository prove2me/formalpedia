-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle
-- name    : Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c7b5d855-7d59-5d90-bc76-7696966e84ee
-- title:
--   Amitsur 1-cocycles of units split when Pic R is trivial
-- statement:
--   Let $R$ be a commutative ring whose Picard group `CommRing.Pic R` is a subsingleton, i.e. trivial, and let $A$ be a commutative $R$-algebra that is faithfully flat as an $R$-module. Let $u$ be a unit of the ring $A \otimes_R A$, and write again $u$ for its underlying element. Consider the three $R$-algebra maps $A \otimes_R A \to A \otimes_R (A \otimes_R A)$ given by `Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeLeft`, which sends $x \otimes y \mapsto x \otimes (y \otimes 1)$, by `Algebra.TensorProduct.includeRight`, which sends $z \mapsto 1 \otimes z$, hence $x \otimes y \mapsto 1 \otimes (x \otimes y)$, and by `Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeRight`, which sends $x \otimes y \mapsto x \otimes (1 \otimes y)$. Assume $u$ satisfies the Amitsur cocycle identity that the product of the images of $u$ under the first two of these maps equals the image of $u$ under the third. Then there exists a unit $a$ of $A$ with $u = a^{-1} \otimes a$ in $A \otimes_R A$.
--
--   This is the faithfully flat form of Hilbert's Theorem 90 for the multiplicative group over a base with trivial Picard group: the first Amitsur (Čech) cohomology of the cover $\operatorname{Spec} A \to \operatorname{Spec} R$ with coefficients in $\mathbb{G}_m$ vanishes, every cocycle being the coboundary of a unit of $A$. It is used in the proof of [`AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted`](thm.html#AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted), in the treatment of $\mathbb{G}_m$ as an fppf sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] [Subsingleton (CommRing.Pic R)]
    {A : Type v} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (u : (A ⊗[R] A)ˣ)
    (hu : Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A) *
        (Algebra.TensorProduct.includeRight : A ⊗[R] A →ₐ[R] A ⊗[R] (A ⊗[R] A)) (u : A ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A)) :
    ∃ a : Aˣ, (u : A ⊗[R] A) = (↑a⁻¹ : A) ⊗ₜ[R] (a : A) := by sorry
