-- Prove2me | Theorems.Thm_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
-- name    : NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/03761c50-5ab9-5d39-84fd-7a2faf30dd32
-- title:
--   Cocycles inflated from F lie in the image of Λ_E
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes containing $p$ (as `pPrime p`), and a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w \mid \exists q \in S,\ q \in w\}$. Let $M$ be a representation of $\Gamma=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, let $\zeta\in\overline{\mathbb Q}$ be a primitive $p$-th root of unity, and let $F\subseteq\overline{\mathbb Q}$ be an intermediate field that is a number field, Galois over $\mathbb Q$, and unramified outside $S$ in the sense that $F/\mathbb Q$ is finite-dimensional and, for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F$; assume $\zeta\in F$ and that the fixing subgroup of $F$ acts trivially on $M$. Let $B$ be a finite $\mathbb Z$-representation of $\mathrm{Gal}(F/\mathbb Q)$ with $p\cdot b=0$ for all $b$, let $\iota_E$ be an additive map from the representation `sUnitsRep` of $S_{\mathbb Q}$-units of $F$ (a subgroup of $\mathrm{Additive}\,F^\times$) to $\mathrm{Additive}\,\overline{\mathbb Q}^\times$ that is induced by the structure map $F\to\overline{\mathbb Q}$ on underlying units, and let $\kappa\colon B\to (M\to \mathrm{Additive}\,\overline{\mathbb Q}^\times)$ be biadditive, equivariant in the sense $\kappa(\rho_B(\gamma|_F)b,\rho_M(\gamma)x)=\gamma\cdot\kappa(b,x)$ for the action of $\Gamma$ on $\overline{\mathbb Q}^\times$, and perfect on the $M$-side: every additive $c\colon B\to\mathrm{Additive}\,\overline{\mathbb Q}^\times$ equals $b\mapsto\kappa(b,x)$ for a unique $x\in M$. Let $\Lambda_E$ be an additive map from $H^1$ of $\mathrm{Gal}(F/\mathbb Q)$ with coefficients in the internal hom from [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73) to the $S_{\mathbb Q}$-unit representation, to `continuousH2S S M`, the quotient of `levelCocyclesS₂ S M` by the preimage of `levelCoboundariesS₂ S M`, and assume $\Lambda_E$ satisfies `IsGlobalBridge₂` for $S$, the restriction homomorphism $\Gamma\to\mathrm{Gal}(F/\mathbb Q)$, the inclusion of the relation module, the free cover [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15), the representation of $\Gamma$ on $\overline{\mathbb Q}^\times$, and the data $\iota_E,\kappa$. Then for every $m\colon\Gamma\times\Gamma\to M$ lying in `levelCocyclesS₂ S M` and satisfying $m(gs,g's')=m(g,g')$ whenever $s,s'$ fix $F$, the class of $m$ in `continuousH2S S M` lies in the image of $\Lambda_E$.
--
--   This is the surjectivity input for the global Tate-duality bridge at the level $F$: every $S$-level degree-two class that is inflated from $\mathrm{Gal}(F/\mathbb Q)$ is realised by $\Lambda_E$, corresponding classically to the realisation of $H^2(G_S,M)$ through $\mathrm{Ext}^2$ of $B$ with $S$-unit coefficients. It is used in the construction of the nondegenerate pairing between the degree-one and degree-two Selmer-type groups for $p\neq 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq.lean

import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_GlobalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation

theorem NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (hζF : ζ ∈ F) (hFM : ∀ s ∈ F.fixingSubgroup, ∀ x : M, M.ρ s x = x)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (x : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b x))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! x : M, ∀ b, κ b x = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M)
    (hmF : ∀ (g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup →
      m (g * s, g' * s') = m (g, g')) :
    ∃ x, ΛE x = continuousH2Sπ S M ⟨m, hm⟩ := by sorry
