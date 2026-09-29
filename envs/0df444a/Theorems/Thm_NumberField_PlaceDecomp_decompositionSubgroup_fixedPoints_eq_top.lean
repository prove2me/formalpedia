-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top
-- name    : NumberField.PlaceDecomp.decompositionSubgroup_fixedPoints_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7cbaf81f-9d27-5918-9f7d-823817f28c79
-- title:
--   Every automorphism over the fixed field stabilises mathcal O_w
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal O_K$. Write $D_w$ for [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation $K \to \Gamma_0$ inside the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, that is, the stabiliser of that valuation subring under the natural action; assume $D_w$ is finite. The group $D_w$ acts on the completion $K_w =$ `w.adicCompletion K`, and let $K_0 \subseteq K_w$ be the subfield of elements fixed by this action. The assertion is that the decomposition subgroup of the valuation subring $\mathcal O_w =$ `w.adicCompletionIntegers K` of $K_w$ relative to the base field $K_0$ — i.e. the stabiliser of $\mathcal O_w$ in the group of $K_0$-algebra automorphisms of $K_w$ — is the whole group $\top$. Equivalently, every automorphism of $K_w$ fixing $K_0$ pointwise carries $\mathcal O_w$ onto itself.
--
--   This is the statement that the local decomposition group of $\mathcal O_w$ over the $D_w$-fixed subfield of $K_w$ is unconditionally full, so that results formulated for a decomposition subgroup of a valuation subring may be instantiated at $\mathcal O_w$ with base field $K_0$. It is used by [`NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints`](thm.html#NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints) in the comparison of global decomposition groups at $w$ with local automorphism groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_decompositionSubgroup_fixedPoints_eq_top.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.decompositionSubgroup_fixedPoints_eq_top (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    (w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)) = ⊤ := by sorry
