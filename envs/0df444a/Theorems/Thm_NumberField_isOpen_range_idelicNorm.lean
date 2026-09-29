-- Prove2me | Theorems.Thm_NumberField_isOpen_range_idelicNorm
-- name    : NumberField.isOpen_range_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/389164c7-860a-537d-bc66-e354a83545f4
-- title:
--   Openness of the idelic norm group N(A_L^×)
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ an algebra over $K$, and let $B$ be an adele base-change datum for $(\mathcal{O}_K,K)$ and $(\mathcal{O}_L,L)$, i.e. a structure consisting of: a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_L$ between the adele rings; the compatibility that for every $e \in K$ the image $\beta(e)$ under the structure map $K \to \mathbb{A}_K$ agrees with the image of $e$ under $K \to L \to \mathbb{A}_L$; an isomorphism of $\mathbb{A}_K$-algebras $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$, where $\mathbb{A}_L$ is regarded as an $\mathbb{A}_K$-algebra via $\beta$; and the requirement that this isomorphism send $1 \otimes f$ to the image of $f$ under $L \to \mathbb{A}_L$ for all $f \in L$. The associated adelic norm is the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$ of this algebra structure, a homomorphism of multiplicative monoids, and the idelic norm attached to $B$ is the induced group homomorphism $\mathbb{A}_L^\times \to \mathbb{A}_K^\times$ on unit groups. The assertion is that the underlying set of the range of this homomorphism, a subgroup of the idele group $\mathbb{A}_K^\times$, is open. No Galois hypothesis on $L/K$ is imposed.
--
--   This is the openness half of the basic topological description of norm groups in global class field theory, the complementary half being the finiteness of the index of $K^\times N(\mathbb{A}_L^\times)$ in $\mathbb{A}_K^\times$. It is what allows continuous characters of $\mathbb{A}_K^\times$ trivial on $K^\times N(\mathbb{A}_L^\times)$ to be treated as characters of a finite discrete quotient, and in this form it is used in the idelic bookkeeping of central characters and of Hecke characters cut out by norm conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_isOpen_range_idelicNorm.lean

import Definitions.Def_M4aHerbrand_AdeleBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.isOpen_range_idelicNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    IsOpen ((B.idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by sorry
