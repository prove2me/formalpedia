-- Prove2me | Theorems.Thm_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
-- name    : Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/1b4e064e-7f59-5422-97f6-6969ff41a17a
-- title:
--   Acyclicity over the residue field gives acyclicity after localisation
-- statement:
--   Let $S$ be a commutative ring, $\mathfrak m \subseteq S$ a maximal ideal and $n$ a natural number. Let $K_i$, $i \in \mathbb N$, be $S$-modules that are finitely generated and projective, with $K_i$ a subsingleton for every $i > n$, and let $\delta_i \colon K_i \to K_{i+1}$ be $S$-linear maps satisfying $\delta_{i+1} \circ \delta_i = 0$ for all $i$. Let $B$ be a field equipped with an $S$-algebra structure such that the structure map $S \to B$ is surjective and $\mathfrak m$ is contained in its kernel. Assume the base-changed complex over $B$ is acyclic in the elementwise sense: every $z \in B \otimes_S K_0$ with $(\delta_0)_B z = 0$ vanishes, and for every $i$ every $z \in B \otimes_S K_{i+1}$ with $(\delta_{i+1})_B z = 0$ lies in the range of $(\delta_i)_B$. The conclusion is the same pair of assertions for the base change along $S \to S_{\mathfrak m}$, the localisation of $S$ at $\mathfrak m$: the map $(\delta_0)_{S_{\mathfrak m}}$ on $S_{\mathfrak m} \otimes_S K_0$ has trivial kernel, and for every $i$ the kernel of $(\delta_{i+1})_{S_{\mathfrak m}}$ is contained in the range of $(\delta_i)_{S_{\mathfrak m}}$.
--
--   This is the passage from acyclicity of a bounded complex of finitely generated projective modules over the residue field at a maximal ideal to acyclicity over the local ring there, the complement to the Nakayama-type criterion over a local ring. It is used in the study of Čech-type complexes attached to a polarisation, where vanishing of a localised cohomology module is deduced from vanishing at a rational point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
    (S : Type u) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
    [∀ i, Module.Finite S (K i)] [∀ i, Module.Projective S (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[S] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (B : Type u) [Field B] [Algebra S B] (hB : Function.Surjective (algebraMap S B))
    (h𝔪 : 𝔪 ≤ RingHom.ker (algebraMap S B))
    (h0 : ∀ z : B ⊗[S] K 0, (δ 0).baseChange B z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : B ⊗[S] K (i + 1)), (δ (i + 1)).baseChange B z = 0 →
      z ∈ LinearMap.range ((δ i).baseChange B)) :
    (∀ z : Localization.AtPrime 𝔪 ⊗[S] K 0, (δ 0).baseChange (Localization.AtPrime 𝔪) z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : Localization.AtPrime 𝔪 ⊗[S] K (i + 1)),
        (δ (i + 1)).baseChange (Localization.AtPrime 𝔪) z = 0 →
          z ∈ LinearMap.range ((δ i).baseChange (Localization.AtPrime 𝔪)) := by sorry
