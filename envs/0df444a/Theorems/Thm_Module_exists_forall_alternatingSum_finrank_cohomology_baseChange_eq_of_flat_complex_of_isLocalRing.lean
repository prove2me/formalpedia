-- Prove2me | Theorems.Thm_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
-- name    : Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/40b26883-8319-56e6-8979-015cdc3fc72f
-- title:
--   Constant Euler characteristic of fibres of a flat complex
-- statement:
--   Let $R$ be a Noetherian local commutative ring, let $C : \mathbb{N} \to \mathrm{Type}$ be a family of flat $R$-modules, and let $d_i : C_i \to C_{i+1}$ be $R$-linear maps with $d_{i+1} \circ d_i = 0$ for all $i$. Assume there is an $n \in \mathbb{N}$ with $C_i$ subsingleton (i.e. zero) for all $i > n$, that $\ker d_0$ is a finite $R$-module, and that for each $i$ the quotient of $\ker d_{i+1}$ by the preimage under the inclusion $\ker d_{i+1} \hookrightarrow C_{i+1}$ of $\operatorname{im} d_i$ — that is, the cohomology $H^{i+1}(C)$ — is a finite $R$-module. The conclusion asserts the existence of an integer $\chi_0$ with the following property: for every field $A$ carrying an $R$-algebra structure, every $A$-module $H_0$ equipped with an $A$-linear isomorphism $H_0 \cong \ker((d_0)\otimes_R A)$, and every family of $A$-modules $H_i$ equipped with surjective $A$-linear maps $\varphi_i : \ker((d_{i+1})\otimes_R A) \to H_i$ whose kernels are exactly the preimages of $\operatorname{im}((d_i)\otimes_R A)$ (so that $H_i$ realises $H^{i+1}(A \otimes_R C)$), one has $$\dim_A H_0 + \sum_{i<n} (-1)^{i+1} \dim_A H_i = \chi_0 .$$ The dimensions are `Module.finrank`, and no finiteness of the $H_i$ is assumed.
--
--   This is Mumford's lemma on the constancy of the Euler characteristic of the fibres of a bounded complex of flat modules with finitely generated cohomology over a Noetherian local ring, stated in all degrees. It is used to prove that the Euler characteristic of the base changes of a locally trivial complex of modules over a presheaf of rings is independent of the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A]
      (H0 : Type u) [AddCommGroup H0] [Module A H0] (_e₀ : H0 ≃ₗ[A] LinearMap.ker ((d 0).baseChange A))
      (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module A (H i)]
      (φ : ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) →ₗ[A] H i)
      (_hφ : ∀ i, Function.Surjective (φ i))
      (_hφker : ∀ i, LinearMap.ker (φ i) =
        (LinearMap.range ((d i).baseChange A)).comap (LinearMap.ker ((d (i + 1)).baseChange A)).subtype),
      (Module.finrank A H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank A (H i) : ℤ) = χ₀ := by sorry
