-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints
-- name    : NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/cc606643-ba28-5b05-a232-bcbda371396b
-- title:
--   Decomposition group at w as Aut of the completion
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $D_w$ for [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation of $K$ inside the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, and assume $D_w$ is finite. Let $K_w$ denote the $w$-adic completion of $K$, $\mathcal{O}_w$ its ring of integers, and let $K_0 = (K_w)^{D_w}$ be the subfield of $K_w$ fixed by the natural action of $D_w$. The assertion is that there exists a group isomorphism $\Phi$ from $D_w$ onto the decomposition subgroup of $\mathcal{O}_w$ in the group of $K_0$-algebra automorphisms of $K_w$ — that is, onto the subgroup of those $\tau \in K_w \simeq_{\mathrm{alg}[K_0]} K_w$ stabilising $\mathcal{O}_w$ — which is compatible with the actions: for every $\sigma \in D_w$ and every $x \in K_w$, the underlying map of the automorphism $\Phi(\sigma)$ sends $x$ to $\sigma \cdot x$.
--
--   This identifies the decomposition group at a finite place $w$, defined as a subgroup of the $E$-automorphisms of $K$, with the full automorphism group of the completion $K_w$ over the fixed subfield, in a way that transports the given action of $D_w$ on $K_w$ into the Galois-theoretic one. It is used to transfer statements about complete discrete valuation rings and their decomposition groups to the $D_w$-modules $K_w^\times$ and $\mathcal{O}_w^\times$, in particular in the computations of the Tate cohomology groups of these modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    ∃ Φ : NumberField.PlaceDecomp.decomp E K w ≃*
        ((w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K))),
      ∀ (σ : NumberField.PlaceDecomp.decomp E K w) (x : w.adicCompletion K),
        ((Φ σ : (w.adicCompletion K) ≃ₐ[FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)] (w.adicCompletion K)) : _) x = σ • x := by sorry
