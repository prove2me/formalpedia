-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic
-- name    : NumberField.PlaceDecomp.iSup_decomp_eq_top_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/9d03fb1c-9b96-5d95-98b0-ad89959be21e
-- title:
--   Decomposition subgroups at finite places generate a cyclic Galois group
-- statement:
--   Let $E$ and $F$ be fields (in the lowest universe) which are number fields, with $F$ an $E$-algebra such that $F/E$ is Galois and the Galois group $F \simeq_{\mathrm{alg}[E]} F$ is cyclic. For a nonzero prime $w$ of the ring of integers $\mathcal{O}_F$, that is an element of the height-one spectrum of $\mathcal{O}_F$, write $\mathcal{O}_w \subseteq F$ for the valuation subring of the $w$-adic valuation on $F$; the subgroup [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) of the Galois group is the decomposition subgroup of $\mathcal{O}_w$ over $E$, i.e. the stabiliser of $\mathcal{O}_w$ under the pointwise action of $E$-algebra automorphisms of $F$ on subrings. The assertion is that the supremum, in the lattice of subgroups of $F \simeq_{\mathrm{alg}[E]} F$, of these decomposition subgroups as $w$ ranges over all nonzero primes of $\mathcal{O}_F$ is the whole group $\top$; equivalently, the decomposition subgroups at the finite places of $F$ generate $\mathrm{Gal}(F/E)$.
--
--   This is the classical statement that the decomposition groups at the finite places generate the Galois group, here in the cyclic case, which is the form used to rule out a nontrivial cyclic extension in which every finite prime splits completely (the "first inequality" step). It feeds into the Herbrand-quotient style argument [`M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic`](thm.html#M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain
open NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.iSup_decomp_eq_top_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)] :
    (⨆ w : HeightOneSpectrum (𝓞 F), NumberField.PlaceDecomp.decomp E F w) = ⊤ := by sorry
