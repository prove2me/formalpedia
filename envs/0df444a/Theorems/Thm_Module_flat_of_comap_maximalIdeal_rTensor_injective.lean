-- Prove2me | Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective
-- name    : Module.flat_of_comap_maximalIdeal_rTensor_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d26b7a39-db96-5f67-a8fc-52a638788984
-- title:
--   Local criterion for flatness at a contracted prime
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, both Noetherian, and suppose $S$ is local with maximal ideal $\mathfrak m_S$. Let $M$ be an abelian group carrying compatible $R$- and $S$-module structures (a scalar tower over $R \to S$) and assume $M$ is finitely generated as an $S$-module. Let $p$ be an ideal of $R$ which is the contraction of $\mathfrak m_S$ along the structure map $R \to S$, i.e. $p = (\mathfrak m_S)^{-1}$ under $\operatorname{algebraMap} R\,S$. Assume that the $R$-linear map $p \otimes_R M \to R \otimes_R M$ obtained by tensoring the inclusion $p \hookrightarrow R$ with $M$ on the right is injective; under the identification $R \otimes_R M \cong M$ this is the statement that $p \otimes_R M \to M$ is injective, equivalently that $\operatorname{Tor}^R_1(R/p, M) = 0$. The conclusion is that $M$ is flat as an $R$-module.
--
--   This is the local criterion for flatness in the Noetherian case, transported to a not necessarily local base $R$ by taking $p$ to be the prime of $R$ contracted from the maximal ideal of the local ring $S$: vanishing of a single $\operatorname{Tor}_1$ against $R/p$ suffices for $R$-flatness of a module finite over $S$. It is used in the study of the flat locus, in particular for the existence of a finitely generated subalgebra over which flatness of a localised tensor product already holds and for the openness of the set of primes at which the localisation is flat.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M := by sorry
