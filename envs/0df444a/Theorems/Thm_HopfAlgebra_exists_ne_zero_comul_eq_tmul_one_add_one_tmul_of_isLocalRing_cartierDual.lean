-- Prove2me | Theorems.Thm_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
-- name    : HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/50d00493-4e54-5bc1-977f-e77bf9ea1a0c
-- title:
--   Non-zero primitive element in a finite unipotent bialgebra
-- statement:
--   Let $k$ be a field and let $A$ be a commutative ring which is a bialgebra over $k$ whose comultiplication is cocommutative, and which is finite as a $k$-module. Two hypotheses are imposed: first, that [`CartierDual k A`](def/HopfAlgebra_CartierDual.html#L12), by definition the $k$-linear dual $\operatorname{Hom}_k(A,k)$ of $A$ with its ring structure as Cartier dual, is a local ring; second, that the $k$-dimension of $A$ is not equal to $1$. The conclusion is that there exists $a \in A$ with $a \neq 0$ whose image under the comultiplication $\Delta \colon A \to A \otimes_k A$ is $a \otimes 1 + 1 \otimes a$; that is, $A$ possesses a non-zero primitive element. Note that no Hopf algebra structure (antipode) on $A$ is required, only the bialgebra structure together with cocommutativity, finiteness, locality of the Cartier dual and non-triviality of the rank.
--
--   In the language of group schemes this says that a non-trivial finite commutative group scheme $G = \operatorname{Spec} A$ over a field whose Cartier dual has local coordinate ring (a unipotent $G$) admits a non-zero homomorphism to the additive group, i.e. a non-zero primitive element of $A$; it is the finite commutative case of the classical characterisation of unipotent group schemes by the existence of non-trivial additive characters. It is used in the study of Dieudonné modules, in particular in the results bounding the $k$-dimension of $A$ and the order of the associated finite group by powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] (hA : IsLocalRing (CartierDual k A)) (hrank : Module.finrank k A ≠ 1) :
    ∃ a : A, a ≠ 0 ∧ Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a := by sorry
