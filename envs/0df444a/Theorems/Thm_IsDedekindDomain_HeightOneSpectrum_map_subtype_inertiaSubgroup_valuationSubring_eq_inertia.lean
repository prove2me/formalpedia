-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
-- name    : IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/185b20dc-58d8-584a-9c8a-588c1ea1b4e2
-- title:
--   Inertia of the w-adic valuation ring equals ideal inertia
-- statement:
--   Let $E$ and $F$ be number fields (fields of characteristic $0$, finite-dimensional over $\mathbb{Q}$) with $F$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$, with associated prime ideal $\mathfrak{P}_w =$ `w.asIdeal`. Write $G = F \simeq_{\mathrm{alg}[E]} F$ for the group of $E$-algebra automorphisms of $F$, and let $A_w \subset F$ be the valuation subring of the $w$-adic valuation of $F$, that is $\{x \in F : w(x) \ge 0\}$. Inside $G$ sit the decomposition subgroup of $A_w$ over $E$, the stabiliser of $A_w$ under the action of $G$, and within it the inertia subgroup of $A_w$ over $E$, consisting of those automorphisms stabilising $A_w$ and inducing the identity on the residue field of $A_w$. The theorem asserts that the image of this inertia subgroup under the inclusion of the decomposition subgroup into $G$ coincides, as a subgroup of $G$, with the inertia subgroup of the ideal $\mathfrak{P}_w$ in $G$, namely the automorphisms $\sigma$ with $\sigma x - x \in \mathfrak{P}_w$ for every $x \in \mathcal{O}_F$.
--
--   This reconciles the two spellings of the inertia group at a finite place of a number field: the valuation-theoretic one, used where ramification groups are set up (the inertia subgroup being the ramification group of index $0$), and the ideal-theoretic one, used in the construction of the idelic Artin map. It is invoked in the Herbrand-function and local-reciprocity steps and in the local analysis of decomposition groups at places of prime residue degree; its proof uses the identification of the stabiliser of $w$ in $F \simeq_{\mathrm{alg}[E]} F$ with the decomposition group of $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.PlaceDecomp

theorem IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    (((w.valuation F).valuationSubring).inertiaSubgroup E).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype =
      w.asIdeal.inertia (F ≃ₐ[E] F) := by sorry
