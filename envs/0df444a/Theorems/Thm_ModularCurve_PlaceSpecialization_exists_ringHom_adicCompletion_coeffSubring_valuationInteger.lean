-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger
-- name    : ModularCurve.PlaceSpecialization.exists_ringHom_adicCompletion_coeffSubring_valuationInteger
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c9cab77f-a522-5995-a384-bf447a7159fa
-- title:
--   Completed A∩ K maps to the valuation ring of widehatℚ̄_A
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$ (the Mathlib algebraic closure of $\mathbb Q$) and let $K$ be an intermediate field of $\mathbb Q \subseteq \overline{\mathbb Q}$. Write $\mathcal O = A \cap K$ for the subring `NodeLocalized.coeffSubring A K`, defined as the infimum of the underlying subring of $A$ and the underlying subring of $K$, and assume $\mathcal O$ is a discrete valuation ring. Let $\widehat{\mathcal O}$ denote the adic completion of $\mathcal O$ with respect to its maximal ideal, and let $C$ be the completion of $\overline{\mathbb Q}$ for the valuation `A.valuation` attached to $A$, with $\mathcal O[C]$ its ring of integers (the elements of valuation at most $1$). The assertion is that there exists a ring homomorphism $j \colon \widehat{\mathcal O} \to \mathcal O[C]$ such that for every $o \in \mathcal O$, the image in $C$ of $j$ applied to the canonical image of $o$ in $\widehat{\mathcal O}$ coincides with the image of $o$ under the canonical map $\overline{\mathbb Q} \to C$. Only existence is asserted; no continuity or uniqueness statement is made.
--
--   This is the completed form of the inclusion $A \cap K \subset \overline{\mathbb Q} \subset C$: it identifies the abstract adic completion of the discrete valuation ring of coefficients with a subring of the valuation ring of the completion of $\overline{\mathbb Q}$ at the place determined by $A$, compatibly with the inclusion of $A\cap K$. It supplies the comparison map used in the analysis of prolongation tuples at a node, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable) and in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open Valued in

theorem ModularCurve.PlaceSpecialization.exists_ringHom_adicCompletion_coeffSubring_valuationInteger
    {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)] :
    ∃ j : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion],
      ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ((o : AlgebraicClosure ℚ) : (A.valuation).Completion) := by sorry
