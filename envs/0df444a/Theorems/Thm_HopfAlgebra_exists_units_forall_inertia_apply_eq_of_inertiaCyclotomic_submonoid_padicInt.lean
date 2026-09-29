-- Prove2me | Theorems.Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
-- name    : HopfAlgebra.exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/44c8f6de-1828-5618-9cb8-749f1956ee13
-- title:
--   Kummer-type splitting of inertia for p-torsion Hopf algebras over ℤₚ
-- statement:
--   Let $p$ be an odd prime and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ that is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Write $M$ for the monoid $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(H, \overline{\mathbb{Q}}_p)$ under convolution (the type `WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)`), and let $I$ denote the inertia subgroup of $\overline{\mathbb{Q}}_p \simeq_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$ attached to the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20), i.e. the image in the full automorphism group of the inertia subgroup of its decomposition subgroup. Assume $f^p = 1$ for every $f \in M$, and let $D \le M$ be a submonoid such that: (i) whenever $\sigma \in I$ and $c \in \mathbb{N}$ satisfy $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^p = 1$, then for $f \in D$ every $g \in M$ with $g(h) = \sigma(f(h))$ for all $h \in H$ equals $f^c$; and (ii) for $\sigma \in I$ and arbitrary $f, g \in M$ with $g(h) = \sigma(f(h))$ there is $d \in D$ with $g = f \cdot d$. Then there exist $t \in \mathbb{N}$ and families $u, \beta : \mathrm{Fin}\, t \to \overline{\mathbb{Q}}_p$ with $\|u_i\| = 1$, each $u_i$ fixed by $I$, and $\beta_i^p = u_i$, such that every $\sigma \in I$ acting trivially on the $p$-th roots of unity and fixing all $\beta_i$ satisfies: for all $f, g \in M$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $g = f$.
--
--   This is the local form over $\mathbb{Z}_p$, $\overline{\mathbb{Q}}_p$ of the Kummer-theoretic description of finite flat commutative group schemes killed by $p$ that are multiplicative-by-étale for inertia: the inertia action on the $\overline{\mathbb{Q}}_p$-points becomes trivial after adjoining $\mu_p$ and the $p$-th roots of finitely many inertia-invariant units. It is used in the analysis of inertia at $p$ for residual Galois representations, feeding into [`ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd`](thm.html#ResidualGaloisRep.unitRootInertia_trivial_and_localFlatClassesAd_le_ordinaryUnitClassesAd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem HopfAlgebra.exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hHp : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1)
    (D : Submonoid (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)))
    (hDcyc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ f ∈ D, ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          (∀ h : H, g h = σ (f h)) → g = f ^ c)
    (hquot : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        (∀ h : H, g h = σ (f h)) → ∃ d ∈ D, g = f * d) :
    ∃ (t : ℕ) (u β : Fin t → PadicAlgCl p),
      (∀ i, ‖u i‖₊ = 1) ∧
      (∀ i, ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → σ (u i) = u i) ∧
      (∀ i, β i ^ p = u i) ∧
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ) → (∀ i, σ (β i) = β i) →
          ∀ f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), (∀ h : H, g h = σ (f h)) → g = f := by sorry
