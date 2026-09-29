-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_chart_equiv_linearMap
-- name    : Module.Grassmannian.exists_chart_equiv_linearMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/82149600-e0da-5350-96fa-c3ee8ee5505f
-- title:
--   Standard Grassmannian chart at a k-tuple as linear maps
-- statement:
--   Fix a commutative ring $R$, an $R$-module $M$, a natural number $k$ and a $k$-tuple $x : \mathrm{Fin}\,k \to M$ of elements of $M$. For a commutative $R$-algebra $A$, write $G(A)$ for Mathlib's `Module.Grassmannian A (A ⊗[R] M) k`, the type of $A$-submodules $N \subseteq A \otimes_R M$ whose quotient is a finitely generated projective $A$-module of rank $k$, and let $U_x(A) \subseteq G(A)$ be the subtype of those $N$ for which the $A$-linear map $(\mathrm{Fin}\,k \to A) \to (A \otimes_R M)/N$, $v \mapsto \sum_i v_i \cdot \overline{1 \otimes x_i}$, is bijective; let $H_x(A)$ be the subtype of $R$-linear maps $\psi : M \to (\mathrm{Fin}\,k \to A)$ with $\psi(x_j) = \mathrm{Pi.single}\,j\,1$ for every $j$. The theorem asserts the existence of a family $\mathrm{pt}$ of equivalences $\mathrm{pt}_A : U_x(A) \simeq H_x(A)$, one for each such $A$, with three properties: (1) for all $A$, all $N \in U_x(A)$ and all $m \in M$, $\sum_i \mathrm{pt}_A(N)(m)_i \cdot \overline{1 \otimes x_i} = \overline{1 \otimes m}$ in $(A \otimes_R M)/N$, so $\mathrm{pt}_A(N)(m)$ is the coordinate vector of the class of $1 \otimes m$; (2) for all $A$ and $\psi \in H_x(A)$, the submodule underlying $\mathrm{pt}_A^{-1}(\psi)$ is the kernel of the $A$-linear extension `ψ.liftBaseChange A` of $\psi$ to $A \otimes_R M$; (3) for every $R$-algebra map $\varphi : A \to B$ and every $N \in U_x(A)$, the base change `Module.Grassmannian.map φ N` again lies in $U_x(B)$, and the coordinates of the resulting point are obtained by applying $\varphi$ to those of $\mathrm{pt}_A(N)$ coefficientwise.
--
--   This is the first step in Grothendieck's construction of the Grassmannian: the standard chart at a $k$-tuple $x$ of the Grassmannian functor is identified, naturally in the test algebra, with the functor of $R$-linear maps $M \to A^k$ carrying $x$ to the standard basis. It is used for the representability of the chart by a quotient of a symmetric algebra, for the computation of Plücker coordinates as determinants, and for the statement that the charts form an open cover of the Grassmannian functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_chart_equiv_linearMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_chart_equiv_linearMap
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1},
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, (pt A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (ψ : {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}),
          ((pt A).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ (m : M) (i : Fin k),
              (pt B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((pt A N).1 m i)) := by sorry
