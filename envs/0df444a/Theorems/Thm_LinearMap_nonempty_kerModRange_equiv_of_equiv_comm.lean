-- Prove2me | Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
-- name    : LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/62b77d33-6aff-5772-bac9-f8a1b217b3e1
-- title:
--   Transfer of ker d⁰ and ker dⁱ⁺¹/im dⁱ along a degreewise isomorphism
-- statement:
--   Let $R$ be a commutative ring and let $C, C' \colon \mathbb{N} \to \mathrm{Type}$ be two families of $R$-modules (each $C i$, $C' i$ an additive commutative group with an $R$-module structure), equipped with $R$-linear maps $d i \colon C i \to C (i+1)$ and $d' i \colon C' i \to C' (i+1)$ for every $i$; no condition $d \circ d = 0$ is imposed, so these are merely sequences of modules and maps. Suppose given $R$-linear isomorphisms $e i \colon C i \simeq C' i$ for every $i$, compatible with the differentials in the sense that $e (i+1)(d i\,x) = d' i (e i\, x)$ for all $i$ and all $x \in C i$. The conclusion is the conjunction of two nonemptiness assertions: first, that there exists an $R$-linear isomorphism $\ker (d 0) \simeq \ker (d' 0)$; and second, that for every $i$ there exists an $R$-linear isomorphism between the quotient of $\ker (d (i+1))$ by the preimage of $\operatorname{range}(d i)$ under the inclusion $\ker (d (i+1)) \hookrightarrow C (i+1)$, i.e. by $\operatorname{range}(d i) \cap \ker (d (i+1))$ viewed inside $\ker (d(i+1))$, and the corresponding quotient formed from $d'$. Both assertions are stated as `Nonempty` of the type of linear equivalences, so no particular isomorphism is named in the conclusion.
--
--   This is the elementary statement that the cohomology of a sequence of modules with linear maps depends only on the sequence up to degreewise isomorphism compatible with the maps. It is recorded in exactly the shape in which Čech-type cohomology of module presheaves and of graded modules on the standard cover of projective space is defined in this development, and is used there to transfer such cohomology along an isomorphism of cochain data, for instance in the computations of Hilbert functions and in the construction of free complexes quasi-isomorphic to Čech complexes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) := by sorry
