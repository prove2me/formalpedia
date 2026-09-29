-- Prove2me | Theorems.Thm_NumberField_exists_isGalois_compositum
-- name    : NumberField.exists_isGalois_compositum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/caf632d8-8905-58db-b5ae-01efc65a3bde
-- title:
--   Existence of a Galois compositum of two Galois number fields
-- statement:
--   Let $E$, $F$, $L$ be number fields (fields of characteristic zero which are finite over $\mathbb{Q}$), with $E$-algebra structures on $F$ and on $L$ making each of $F/E$ and $L/E$ Galois. The assertion is that there exists a type $N$ together with a field structure, a `NumberField` structure, and algebra structures of $E$, of $F$ and of $L$ on $N$, such that the two towers $E \to F \to N$ and $E \to L \to N$ are compatible (both `IsScalarTower` conditions, i.e. the structure maps $E \to N$ factor through $F$ and through $L$ respectively), with the two properties: $N/E$ is Galois, and every $E$-algebra automorphism $\sigma$ of $N$ which fixes the image of $F$ pointwise, $\sigma(\mathrm{alg}_F(x)) = \mathrm{alg}_F(x)$ for all $x \in F$, and fixes the image of $L$ pointwise, $\sigma(\mathrm{alg}_L(y)) = \mathrm{alg}_L(y)$ for all $y \in L$, equals the identity. The last clause says that $\mathrm{Gal}(N/F) \cap \mathrm{Gal}(N/L)$ is trivial in $\mathrm{Gal}(N/E)$, i.e. $N$ is generated over $E$ by the two images: $N = F\cdot L$. Note that the embeddings are supplied only as algebra structures, not as named maps.
--
--   This is the existence of the compositum $FL$ of two finite Galois extensions of a number field, packaged as an abstract number field with compatible algebra structures rather than as a subfield of a fixed algebraic closure. It is consumed by constructions that quantify over abstract number fields, in particular in the Herbrand-quotient and fundamental-class computations of global class field theory, where a given Galois layer is composed with an auxiliary cyclotomic layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isGalois_compositum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_isGalois_compositum
    (E F L : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra E F] [Algebra E L] [IsGalois E F] [IsGalois E L] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra E N) (_ : Algebra F N) (_ : Algebra L N)
      (_ : IsScalarTower E F N) (_ : IsScalarTower E L N),
      IsGalois E N ∧
      ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
        (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1 := by sorry
