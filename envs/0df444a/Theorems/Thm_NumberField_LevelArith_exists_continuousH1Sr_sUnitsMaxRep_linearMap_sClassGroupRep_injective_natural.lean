-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
-- name    : NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/06806f5f-4282-5f3d-b7bd-e40945455687
-- title:
--   Equivariant embedding of H¹_S into the S-class group
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of rational primes with $p \in S$ (via `pPrime p`), and let $L$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is finite over $\mathbb Q$ and satisfies `IsUnramifiedOutside S`: $L/\mathbb Q$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a non-unit, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ is contained in the fixing subgroup of $L$. The assertion is that there exists a $\mathbb Z$-linear map $f$ from `continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)`, the image under `H1π` of the cocycle submodule `levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)` inside $H^1$ of the representation of $L$'s fixing subgroup $\mathrm{Gal}(\overline{\mathbb Q}/L)$ on the additive group of the stable subgroup `sUnitsMaxStable S L` of $\overline{\mathbb Q}^{\times}$, to the module underlying `sClassGroupRep ↥L ↥L (S : Set Nat.Primes)`, the quotient of the additive class group of $\mathcal O_L$ by the submodule attached to the subgroup `sPrimeClasses ↥L ↥L S` of classes of primes above the primes in $S$, such that: $f$ is injective; $f$ maps the $p$-torsion submodule of the source exactly onto the $p$-torsion submodule of the target; and $f$ is natural in the following cocycle-wise sense. For every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and every $\tau \in \mathrm{Aut}(L/\mathbb Q)$ with $\sigma(y) = \tau(y)$ for all $y \in L$, and for all $c, c'$ in `levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)` satisfying the relation that whenever $s, s' \in \mathrm{Gal}(\overline{\mathbb Q}/L)$ obey $\sigma^{-1} s \sigma = s'$ one has $c'(s) = \sigma \cdot c(s')$ as units of $\overline{\mathbb Q}$, and for every ideal class $C$ of $\mathcal O_L$: if $f$ of the $H^1$-class of $c$ is the class of $C$ in the quotient, then $f$ of the $H^1$-class of $c'$ is the class of $\tau \cdot C$.
--
--   This is the Kummer-theoretic comparison of the $S$-ramified first cohomology of the $S$-units with the $S$-class group of $L$, in the form of an injection matching $p$-torsion and commuting with the action of automorphisms of $L$ lifted to $\overline{\mathbb Q}$. It is used in the computation of the $p$-torsion of the corresponding $H^2$, feeding [`groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso`](thm.html#groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] :
    ∃ f : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →ₗ[ℤ] (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)),
      Function.Injective f ∧
        Submodule.map f (Submodule.torsionBy ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) =
          Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ) ∧
        ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L),
          (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
          ∀ (c c' : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
            (∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' →
              sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s')) →
            ∀ C : ClassGroup (𝓞 ↥L),
              f ⟨(H1π (sUnitsMaxRep S L)).hom c.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c.2⟩ =
                  Submodule.Quotient.mk (Additive.ofMul C) →
              f ⟨(H1π (sUnitsMaxRep S L)).hom c'.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c'.2⟩ =
                  Submodule.Quotient.mk (Additive.ofMul (τ • C)) := by sorry
