-- Prove2me | Theorems.Thm_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
-- name    : IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7a20be1f-0bb8-5dd8-9d9b-c7a61c446afe
-- title:
--   Schlessinger comparison of fibre products for a flat algebra
-- statement:
--   Let $T'$ be a commutative local ring, $I \subseteq \mathfrak m$ an ideal contained in the maximal ideal with $I\cdot\mathfrak m = 0$, and write $k = \mathrm{ResidueField}\,T'$. Let $V$ be an abelian group carrying commuting left and right $k$-module structures that agree, together with a $T'$-module structure compatible with the $k$-structure via the residue map, and let $\iota \colon V \to T'$ be an injective $T'$-linear map whose range is exactly $I$ (viewed as a $T'$-submodule). Let $C$ be a commutative $T'$-algebra which is flat over $T'$. Put $\sigma \colon C \to C/IC$ for the quotient map, and let $P \subseteq C \times C$ be the subring where the two projections agree modulo $IC$, i.e. the fibre product $C \times_{C/IC} C$. Let $C_k = k \otimes_{T'} C$ with $\mathrm{toCk} \colon C \to C_k$ the inclusion of the right factor, let $E = C_k \otimes_k \mathrm{TrivSqZeroExt}\,k\,V = C_k \otimes_k k[V]$, and let $\mathrm{aug} \colon E \to C_k$ be the algebra map given by the identity on $C_k$ and by the first-coordinate projection $k[V] \to k$ followed by the structure map $k \to C_k$. Let $Q \subseteq C \times E$ be the subring where $\mathrm{toCk}$ on the first coordinate agrees with $\mathrm{aug}$ on the second, i.e. $C \times_{C_k} E$. The assertion is that there is a ring isomorphism $\Theta \colon P \cong Q$ which preserves the first coordinate in $C$, sends each diagonal element $(a,a) \in P$ to second coordinate $\mathrm{toCk}(a) \otimes 1$, and sends each element of the form $(0, \iota(v)c) \in P$ (for $v \in V$, $c \in C$, with $\iota(v)$ taken in $C$ along the structure map) to second coordinate $\mathrm{toCk}(c) \otimes \mathrm{inr}(v)$.
--
--   This is the ring-theoretic core of Schlessinger's identification $C \times_{C/IC} C \cong C \times_{C_k} (C_k \otimes_k k[V])$ for a small ideal $I$, relativised from $C = T'$ to an arbitrary flat $T'$-algebra $C$. It underlies the construction and uniqueness of tangent-vector data for small extensions in the deformation-theoretic part of the argument, being used by the results on tangent pairs for flat algebras over a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u

theorem IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C] :
    let k := ResidueField T'
    let σ : C →+* C ⧸ I.map (algebraMap T' C) := Ideal.Quotient.mk _
    let P : Subring (C × C) := RingHom.eqLocus (σ.comp (RingHom.fst C C)) (σ.comp (RingHom.snd C C))
    let toCk : C →+* k ⊗[T'] C := Algebra.TensorProduct.includeRight.toRingHom
    let E := (k ⊗[T'] C) ⊗[k] TrivSqZeroExt k V
    let aug : E →+* k ⊗[T'] C :=
      (Algebra.TensorProduct.lift (AlgHom.id k (k ⊗[T'] C))
        ((Algebra.ofId k (k ⊗[T'] C)).comp (TrivSqZeroExt.fstHom k k V)) (fun _ _ => Commute.all _ _)).toRingHom
    let Q : Subring (C × E) := RingHom.eqLocus (toCk.comp (RingHom.fst C E)) (aug.comp (RingHom.snd C E))
    ∃ Θ : P ≃+* Q,
      (∀ x : P, ((Θ x : Q) : C × E).1 = (x : C × C).1) ∧
      (∀ (a : C) (ha : (a, a) ∈ P), ((Θ ⟨(a, a), ha⟩ : Q) : C × E).2 = toCk a ⊗ₜ (1 : TrivSqZeroExt k V)) ∧
      (∀ (v : V) (c : C) (h : ((0 : C), algebraMap T' C (ι v) * c) ∈ P),
        ((Θ ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩ : Q) : C × E).2 = toCk c ⊗ₜ TrivSqZeroExt.inr v) := by sorry
