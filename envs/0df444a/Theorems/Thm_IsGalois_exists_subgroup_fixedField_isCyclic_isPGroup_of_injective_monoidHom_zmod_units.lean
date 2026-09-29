-- Prove2me | Theorems.Thm_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
-- name    : IsGalois.exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/de314a8c-2c85-5f9a-b453-a55bf548d728
-- title:
--   Cyclic p-power quotient of a subgroup of (ℤ/p^k)^×
-- statement:
--   Let $E \subseteq C$ be fields with $C$ a finite-dimensional Galois extension of $E$, let $p$ be a prime and $k$ a natural number, and let $\chi \colon \mathrm{Gal}(C/E) = (C \simeq_{\mathrm{alg}[E]} C) \to (\mathbb{Z}/p^k)^\times$ be an injective group homomorphism. The assertion is the existence of a subgroup $M$ of $\mathrm{Gal}(C/E)$, together with a proof that $M$ is normal, such that: every $g \in \mathrm{Gal}(C/E)$ with $\chi(g) = -1$ lies in $M$; the cardinality of $M$ is at most $2(p-1)$ (truncated subtraction in $\mathbb{N}$); the fixed field $C^{M}$, viewed as an intermediate field of $C/E$, is Galois over $E$; the group $C^{M} \simeq_{\mathrm{alg}[E]} C^{M}$ of $E$-automorphisms of $C^{M}$ is cyclic and is a $p$-group; and $\lvert \mathrm{Aut}_E(C^{M}) \rvert \cdot \lvert M \rvert = \lvert \mathrm{Gal}(C/E) \rvert$, all cardinalities being taken as `Nat.card`. Note that $k$ occurs only through the target of $\chi$, and that the bound $2(p-1)$ is asserted without distinguishing the cases $p = 2$ and $p$ odd.
--
--   This is the group-theoretic half of Artin's device for extracting, from a Galois extension with cyclic character values in $(\mathbb{Z}/p^k)^\times$, a subextension with cyclic $p$-power Galois group in which the prescribed involutions (the elements of character $-1$, e.g. complex conjugations in a cyclotomic setting) act trivially. It is used in the construction of auxiliary cyclic $p$-power extensions of number fields inside cyclotomic fields, via [`NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp`](thm.html#NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000

theorem IsGalois.exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
    (E C : Type) [Field E] [Field C] [Algebra E C] [FiniteDimensional E C] [IsGalois E C]
    (p k : ℕ) [Fact p.Prime] (χ : (C ≃ₐ[E] C) →* (ZMod (p ^ k))ˣ) (hχ : Function.Injective χ) :
    ∃ (M : Subgroup (C ≃ₐ[E] C)) (_ : M.Normal),
      (∀ g : C ≃ₐ[E] C, χ g = -1 → g ∈ M) ∧
      Nat.card M ≤ 2 * (p - 1) ∧
      IsGalois E (IntermediateField.fixedField M) ∧
      IsCyclic ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      IsPGroup p ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      Nat.card ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) * Nat.card M = Nat.card (C ≃ₐ[E] C) := by sorry
