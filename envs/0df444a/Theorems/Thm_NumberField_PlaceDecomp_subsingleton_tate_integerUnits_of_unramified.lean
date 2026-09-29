-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified
-- name    : NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/d765c874-9a00-5716-9e32-1e417182b89b
-- title:
--   Vanishing Tate cohomology of local units at unramified places
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $D_w$ for [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup, inside the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, of the valuation subring of the $w$-adic valuation of $K$; assume $D_w$ is finite and cyclic. Let $\mathcal{O}_w =$ `w.adicCompletionIntegers K` be the valuation subring of the $w$-adic completion, on whose unit group $\mathcal{O}_w^{\times}$ the group $D_w$ acts by multiplicative distributive automorphisms. Assume the unramifiedness hypothesis in elementwise form: any $\sigma \in D_w$ with $\sigma \cdot a - a$ in the maximal ideal of $\mathcal{O}_w$ for every $a \in \mathcal{O}_w$ equals $1$. Then, for the representation `Rep.ofMulDistribMulAction` of $D_w$ on $\mathcal{O}_w^{\times}$, both Tate groups in degrees $0$ and $-1$ are subsingletons: the quotient of the invariants by the image of the norm map $\overline{N}$ induced on coinvariants, and the kernel of $\overline{N}$, each have at most one element.
--
--   This is the statement that the units of an unramified local field are cohomologically trivial for the (cyclic) decomposition group in the two Tate degrees relevant to the idelic computations. It is used in the analysis of the Tate cohomology of $S$-idèle modules, where the unramifiedness condition is quoted elementwise for places outside $S$, and in the variant phrased via ramification index one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)] [IsCyclic (NumberField.PlaceDecomp.decomp E K w)]
    (hur : ∀ σ : NumberField.PlaceDecomp.decomp E K w,
      (∀ a : w.adicCompletionIntegers K, σ • a - a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) → σ = 1) :
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateH0 ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateHneg1 := by sorry
