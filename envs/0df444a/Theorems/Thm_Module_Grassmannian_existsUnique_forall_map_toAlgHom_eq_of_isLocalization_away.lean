-- Prove2me | Theorems.Thm_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
-- name    : Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/4f79aaf8-49b1-54f8-9eb2-f8c0bef3f1cc
-- title:
--   Zariski gluing for the Grassmannian functor over standard opens
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module and $k$ a natural number; for a commutative $R$-algebra $A$ write $\mathrm{Gr}_k(A)$ for `Module.Grassmannian A (A ⊗[R] M) k`, the type of $A$-submodules of $A \otimes_R M$ whose quotient is projective of rank $k$, with functoriality in the algebra given by `Module.Grassmannian.map` along an $R$-algebra map. Let $A$ be a commutative $R$-algebra, $n$ a natural number and $f : \mathrm{Fin}\,n \to A$ a family whose image spans the unit ideal of $A$. For each $i$ let $B_i$ be a commutative ring that is simultaneously an $A$-algebra and an $R$-algebra, compatibly ($R \to A \to B_i$ a scalar tower), and which is a localisation of $A$ away from $f_i$; let $N_i \in \mathrm{Gr}_k(B_i)$ be given. Assume the gluing condition: for all $i, j$, every commutative ring $C$ which is an $A$-algebra and an $R$-algebra compatibly and is a localisation of $A$ away from $f_i f_j$, and all $A$-algebra homomorphisms $\rho_1 : B_i \to C$ and $\rho_2 : B_j \to C$, the images of $N_i$ under $\rho_1$ and of $N_j$ under $\rho_2$, viewed as maps of $R$-algebras, agree in $\mathrm{Gr}_k(C)$. Then there is exactly one $N_0 \in \mathrm{Gr}_k(A)$ whose image under the structure map $A \to B_i$ equals $N_i$ for every $i$.
--
--   This is the sheaf axiom for the Grassmannian functor $\mathrm{Gr}_k$ of a module with respect to a standard open covering $\operatorname{Spec} A = \bigcup_i D(f_i)$: compatible sections over the $D(f_i)$ glue uniquely. It is one of the inputs to the construction of the Grassmannian as a scheme by gluing affine charts, used by [`Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`](thm.html#Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A) (hf : Ideal.span (Set.range f) = ⊤)
    (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
    [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
    (N : ∀ i, Module.Grassmannian (B i) (B i ⊗[R] M) k)
    (hN : ∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
        [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
        Module.Grassmannian.map (ρ₁.restrictScalars R) (N i) =
          Module.Grassmannian.map (ρ₂.restrictScalars R) (N j)) :
    ∃! N₀ : Module.Grassmannian A (A ⊗[R] M) k,
      ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i)) N₀ = N i := by sorry
