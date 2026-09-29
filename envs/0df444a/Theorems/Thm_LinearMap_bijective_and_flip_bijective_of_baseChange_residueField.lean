-- Prove2me | Theorems.Thm_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField
-- name    : LinearMap.bijective_and_flip_bijective_of_baseChange_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ed48b61a-bf6f-587a-a087-4173a30b80b1
-- title:
--   Perfectness of a pairing descends from the residue field
-- statement:
--   Let $R$ be a commutative local ring and $k$ a field equipped with an $R$-algebra structure whose structure map $R \to k$ is surjective (hypothesis `hπ`), so that $k$ is the residue field of $R$. Let $M$ and $N$ be $R$-modules that are free and finite over $R$, and let $M_k$, $N_k$ be $k$-vector spaces. Given an $R$-bilinear pairing $B \colon M \to N \to R$, a $k$-bilinear pairing $B_k \colon M_k \to N_k \to k$, and $k$-linear isomorphisms $e_M \colon k \otimes_R M \xrightarrow{\sim} M_k$ and $e_N \colon k \otimes_R N \xrightarrow{\sim} N_k$ which are compatible with the pairings in the sense that $B_k(e_M(1 \otimes m), e_N(1 \otimes n))$ is the image of $B(m,n)$ under $R \to k$ for all $m \in M$, $n \in N$, assume that both $B_k$ and its flip are bijective, i.e. that the two adjoint maps $M_k \to \operatorname{Hom}_k(N_k, k)$ and $N_k \to \operatorname{Hom}_k(M_k, k)$ are bijective. The conclusion is that $B$ and its flip are bijective, i.e. that the adjoints $M \to \operatorname{Hom}_R(N, R)$, $m \mapsto B(m, -)$, and $N \to \operatorname{Hom}_R(M, R)$, $n \mapsto B(-, n)$, are both bijective.
--
--   This is the standard criterion that a bilinear pairing of finite free modules over a local ring is perfect as soon as its reduction to the residue field is perfect, the passage from surjectivity to bijectivity resting on Nakayama's lemma together with the fact that a surjective endomorphism of a finitely generated module is injective. It is used to establish perfectness of the integral Serre duality pairing attached to a two-fold affine open cover of a scheme, in [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w₁ w₂ w₁' w₂'

open scoped TensorProduct

theorem LinearMap.bijective_and_flip_bijective_of_baseChange_residueField
    {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k]
    {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk]
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (hπ : Function.Surjective (algebraMap R k))
    (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k)
    (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk)
    (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n))
    (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) :
    Function.Bijective B ∧ Function.Bijective B.flip := by sorry
