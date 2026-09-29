-- Prove2me | Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
-- name    : Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/dae2f705-4a1f-5c60-9bbc-8283613e58bc
-- title:
--   Two-term free model computing ker d⁰ after base change
-- statement:
--   Let $R$ be a commutative Noetherian ring, and let $C \colon \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each flat over $R$, equipped with $R$-linear maps $d_i \colon C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$, so that $(C, d)$ is a cochain complex indexed by $\mathbb{N}$. Assume there is $n \in \mathbb{N}$ with $C_i$ a subsingleton (that is, zero) for all $i > n$; that $\ker d_0$ is a finitely generated $R$-module; and that for every $i$ the quotient of $\ker d_{i+1}$ by the preimage of $\operatorname{range} d_i$ under the inclusion $\ker d_{i+1} \hookrightarrow C_{i+1}$ — the cohomology $H^{i+1}(C)$ — is a finitely generated $R$-module. The conclusion asserts the existence of a two-term complex $G$, consisting of two finite free $R$-modules $G.C_0$, $G.C_1$ and an $R$-linear map $G.d \colon G.C_0 \to G.C_1$, together with $R$-linear maps $\iota_0 \colon G.C_0 \to C_0$ and $\iota_1 \colon G.C_1 \to C_1$ and a proof of commutativity $d_0 \circ \iota_0 = \iota_1 \circ G.d$, such that for every commutative $R$-algebra $A$ the map $\ker(G.d \otimes_R A) \to \ker(d_0 \otimes_R A)$ obtained by restricting $\iota_0 \otimes_R A$ (which lands in the target kernel by the commutativity) is bijective.
--
--   This is Mumford's lemma on bounded flat complexes with finitely generated cohomology over a Noetherian ring, in its degree-zero form with the comparison map on kernels made explicit: the formation of $H^0$ of $C \otimes_R A$ is computed, uniformly in the $R$-algebra $A$, by a single two-term complex of finite free modules. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules), where the finite free model lets fibre ranks of $H^0$ be read off from a map between free modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C 0) (ι1 : G.C1 →ₗ[R] C 1)
      (comm : d 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d (d 0) ι0 ι1 comm A) := by sorry
