-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
-- name    : MvPolynomial.CrossingQuotient.surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/cfcbb01f-b5ed-5422-80b1-bc5b950e9a7f
-- title:
--   Residue field surjectivity at a crossing point of UV=a
-- statement:
--   Let $O$ be a commutative ring and $a \in O$, and let $Q = \mathrm{MvPolynomial}\,(\mathrm{Fin}\,2)\,O / (X_0X_1 - a)$ be the crossing quotient `CrossingQuotient O a`, so that `CrossingQuotient.crossingScheme a` is the affine scheme $\operatorname{Spec} Q$. Let $q$ be a point of this scheme, i.e. a prime ideal $q.\mathrm{asIdeal}$ of $Q$, and assume that the two elements `CrossingQuotient.U a` and `CrossingQuotient.V a` — the classes in $Q$ of the coordinate variables $X_0$ and $X_1$ — both lie in $q.\mathrm{asIdeal}$. Consider the morphism of schemes $\operatorname{Spec} Q \to \operatorname{Spec} O$ obtained by applying $\operatorname{Spec}$ to the structure map $O \to Q$, and its induced map on residue fields at $q$, a homomorphism $\kappa(\text{image of } q) \to \kappa(q)$ of residue fields of the local rings of the two schemes at the corresponding points. The assertion is that the underlying function of this homomorphism is surjective. Since a homomorphism of fields is injective, it is then an isomorphism, but the Lean statement asserts only surjectivity.
--
--   This records the local structure of a crossing $UV = a$ at a point of the singular locus: there the residue field does not grow over the base. It is used in the analysis of the Deligne–Rapoport model of the modular curve, where crossing charts are compared with the base, in [`ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart`](thm.html#ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart) and [`ModularCurve.XHDRModelAtP.injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart`](thm.html#ModularCurve.XHDRModelAtP.injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
    {O : Type} [CommRing O] (a : O) (q : ↥(CrossingQuotient.crossingScheme a))
    (hU : CrossingQuotient.U a ∈ q.asIdeal) (hV : CrossingQuotient.V a ∈ q.asIdeal) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O a)))).residueFieldMap q).hom := by sorry
