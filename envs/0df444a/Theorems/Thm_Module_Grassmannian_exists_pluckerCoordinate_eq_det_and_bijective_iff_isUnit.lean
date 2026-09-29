-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit
-- name    : Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/f36f7946-724d-5e17-9c6a-e1b5451d10fc
-- title:
--   Plücker coordinates on the standard Grassmannian charts
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module and $k$ a natural number. For a commutative $R$-algebra $A$, write $G$ for `Module.Grassmannian A (A ⊗[R] M) k`, the type of $A$-submodules $N \subseteq A \otimes_R M$ admitted by that Mathlib definition, and for $x : \mathrm{Fin}\,k \to M$ say that $N$ lies in the chart at $x$ when $v \mapsto \sum_i v_i \cdot [1 \otimes x_i]$ is a bijection $A^{k} \to (A \otimes_R M)/N$, the classes being taken along the quotient map `N.toSubmodule.mkQ`. The theorem asserts the existence of a rule $P$ assigning to every such $A$, every $x$, every pair consisting of an $N \in G$ together with a proof that $N$ lies in the chart at $x$, and every $y : \mathrm{Fin}\,k \to M$, an element $P_A(x,N)(y) \in A$, subject to six conditions: (i) for every $m \in M$, $\sum_i P_A(x,N)(x \text{ with } x_i \text{ replaced by } m)\,[1 \otimes x_i] = [1 \otimes m]$; (ii) $P_A(x,N)(y)$ equals the determinant of the $k \times k$ matrix with $(i,j)$ entry $P_A(x,N)(x \text{ with } x_i \text{ replaced by } y_j)$; (iii) $P_A(x,N)(x) = 1$; (iv) for every $R$-algebra homomorphism $\varphi : A \to B$, the submodule `Module.Grassmannian.map φ N` lies in the chart at $x$ over $B$, and for that chart point $P_B(x,\cdot)(y) = \varphi(P_A(x,N)(y))$ for all $y$; (v) $N$ lies in the chart at $y$ if and only if $P_A(x,N)(y)$ is a unit of $A$; and (vi) if $N$ lies in the chart at $y$, then for every $z$ one has $P_A(x,N)(z) = P_A(x,N)(y) \cdot P_A(y,N)(z)$, the second factor taken with respect to the chart at $y$.
--
--   These are the transition data of the Plücker embedding of the Grassmannian functor: the coordinate expansion and minor formula identify $P_x(N)(y)$ with a $k \times k$ minor of the coordinate matrix, the chart at $y$ is cut out inside the chart at $x$ by invertibility of that minor, and the multiplicative relation is the associated cocycle. The result is used in establishing that the Grassmannian functor, once represented, admits a closed immersion into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) :
    ∃ P : ∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M),
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} → (Fin k → M) → A,
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, P A x N (Function.update x i m) • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M),
          P A x N y = (Matrix.of fun i j => P A x N (Function.update x i (y j))).det) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          P A x N x = 1) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ y : Fin k → M, P B x ⟨Module.Grassmannian.map φ N.1, h⟩ y = φ (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M),
          (Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] y i)) ↔ IsUnit (P A x N y)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A] (x : Fin k → M)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (y : Fin k → M)
          (hy : Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] y i))
          (z : Fin k → M),
          P A x N z = P A x N y * P A y ⟨N.1, hy⟩ z) := by sorry
