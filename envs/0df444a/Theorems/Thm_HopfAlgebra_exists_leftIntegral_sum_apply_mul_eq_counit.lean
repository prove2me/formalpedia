-- Prove2me | Theorems.Thm_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit
-- name    : HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b460a72d-daa7-596c-a91b-7856001831c7
-- title:
--   Left integrals representing the counit on a finite free Hopf algebra
-- statement:
--   Let $R$ be a commutative ring and let $B$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which, as an $R$-module, is finite and free. The assertion is that there exist a natural number $n$, a family $\Lambda : \mathrm{Fin}\,n \to \operatorname{Hom}_R(B,R)$ of $R$-linear functionals on $B$, and a family $u : \mathrm{Fin}\,n \to B$ of elements of $B$, such that two conditions hold. First, each $\Lambda_j$ is a left integral in the following explicit sense: for every $b \in B$, applying $\mathrm{id}_B \otimes \Lambda_j$ to the comultiplication $\Delta b \in B \otimes_R B$ and then the canonical isomorphism $B \otimes_R R \cong B$ yields $\Lambda_j(b)\cdot 1_B$; in Sweedler notation, $\sum b_{(1)}\,\Lambda_j(b_{(2)}) = \Lambda_j(b)\,1_B$. Second, the family $(\Lambda_j, u_j)$ represents the counit: for every $b \in B$ one has $\sum_{j} \Lambda_j(u_j\, b) = \varepsilon(b)$, where $\varepsilon$ is the counit of $B$. No bound on $n$ is claimed, and in particular a single integral is not asserted to suffice.
--
--   This is the ring-theoretic form of the Larson–Sweedler theorem on the existence of integrals, in the shape needed for finite flat group schemes: the integrals together with the elements $u_j$ express the counit through multiplication in $B$. It is used in the study of the augmentation ideal of a finite free Hopf algebra and in establishing the Hopf–Galois property for surjections, through [`HopfAlgebra.finite_projective_hopfKer_of_surjective`](thm.html#HopfAlgebra.finite_projective_hopfKer_of_surjective) and [`HopfAlgebra.isHopfGalois_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) • (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b := by sorry
