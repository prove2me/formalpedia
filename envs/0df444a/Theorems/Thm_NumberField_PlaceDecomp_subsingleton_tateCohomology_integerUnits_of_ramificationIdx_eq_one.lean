-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
-- name    : NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/d1c93bee-0b47-5242-9068-5d5674c2ec26
-- title:
--   Tate cohomology of local units vanishes at unramified places
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra such that $K/E$ is Galois, let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $\mathrm{decomp}\,E\,K\,w$ denote the decomposition subgroup of $K \simeq_{\mathrm{alg}[E]} K$ attached to the valuation subring of the $w$-adic valuation of $K$, assumed finite. Assume that the ramification index $e$ of $w$ over the prime $w \cap \mathcal{O}_E$ lying under it equals $1$, and let $q$ be an arbitrary integer. Then the $q$-th Tate cohomology of the representation obtained from the multiplicative action of this decomposition group on the unit group $(\mathcal{O}_{K_w})^{\times}$ of the $w$-adic completion integers is a subsingleton, i.e. vanishes. Here the Tate cohomology in degree $q$ is: ordinary group cohomology $H^{n+1}$ for $q = n+1 > 0$; the invariants modulo the image of the norm map for $q = 0$; the kernel of the norm map for $q = -1$; and group homology $H_{n+1}$ for $q = -(n+2)$.
--
--   This is the statement that the local units at a place unramified in $K/E$ form a cohomologically trivial module for the decomposition group, in all Tate degrees; classically it is the vanishing underlying the computation of local norm indices and Herbrand-quotient arguments. It is used in the project's treatment of Herbrand quotients for ideles, in the vanishing of cohomology of products of coinduced local unit modules, and in level-arithmetic computations with principal ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)]
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) (q : ℤ) :
    Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology q) := by sorry
