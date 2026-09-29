-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_smul_algebraMap
-- name    : NumberField.PlaceDecomp.smul_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/b54bc0b8-e469-5ac5-a154-2bc3646aab07
-- title:
--   Decomposition-group action on K_w extends that on K
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and an $E$-algebra, and let $w$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, i.e. a nonzero prime ideal. Write $K_w$ for the $w$-adic completion `w.adicCompletion K`, carrying the canonical structure map `algebraMap K (w.adicCompletion K)`. Let $\sigma$ be an element of the subgroup `decomp E K w` of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, namely the decomposition subgroup of the valuation subring attached to the $w$-adic valuation of $K$ (the automorphisms over $E$ that preserve that valuation subring); this subgroup acts on $K_w$ by the action supplied by the place-decomposition module. The assertion is that for every $x \in K$, applying $\sigma$ to the image of $x$ in $K_w$ gives the image in $K_w$ of the element $\sigma(x) \in K$, where $\sigma$ is regarded as an $E$-algebra automorphism of $K$ via the coercion from the subgroup. In other words, the structure map $K \to K_w$ is equivariant for the decomposition subgroup.
--
--   This is the compatibility of the decomposition-group action on a completion $K_w$ with the Galois action on the global field $K$, stated for the canonical algebra map $K \to K_w$ in the form used downstream. It is invoked in the local-global comparisons of the project, for instance when adèlic or automorphic-form arguments must descend a Galois-equivariant statement from $K_w$ to $K$, and in the computation of norms of differences $\sigma(x) - x$ at places of ramification index one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_smul_algebraMap.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.smul_algebraMap (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : NumberField.PlaceDecomp.decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by sorry
