-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
-- name    : IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/8d7fe301-1cbf-5e9d-be1e-aec9036f6e21
-- title:
--   Stabiliser of a prime equals its valuation ring's decomposition group
-- statement:
--   Let $E$ and $F$ be fields, each equipped with a number field structure, with $F$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$, i.e. a point of `HeightOneSpectrum (𝓞 F)`, with underlying prime ideal `w.asIdeal` $= \mathfrak{P}_w \subset \mathcal{O}_F$. The group $F \simeq_{alg[E]} F$ of $E$-algebra automorphisms of $F$ acts on $\mathcal{O}_F$ and hence pointwise on its ideals, and it also acts pointwise on subrings of $F$. The assertion is an equality of subgroups of $F \simeq_{alg[E]} F$: the stabiliser of the ideal $\mathfrak{P}_w$ for the pointwise action coincides with the decomposition subgroup over $E$ of the valuation subring $\{x \in F : |x|_w \le 1\}$ attached to the $w$-adic valuation `w.valuation F` on $F$, that is, with the stabiliser of that valuation subring under the pointwise action. No Galois or separability hypothesis is imposed beyond what the number field structures supply; the two subgroups are equal as subgroups, not merely equal in cardinality.
--
--   This is the standard bridge between the ideal-theoretic and the valuation-theoretic description of the decomposition group at a finite place: $\sigma(\mathfrak{P}_w) = \mathfrak{P}_w$ if and only if $\sigma$ preserves the valuation ring $A_w$. It lets results stated for decomposition and ramification subgroups of valuation subrings be transported to statements about Galois stabilisers of prime ideals, and is used in the treatment of lower and upper ramification groups, of local contributions to Artin conductors, and in the idelic description of the Artin map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.PlaceDecomp Pointwise

theorem IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal = ((w.valuation F).valuationSubring).decompositionSubgroup E := by sorry
