-- Prove2me | Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
-- name    : NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7b221f6f-f37c-5fc3-a8f7-33c052b335b8
-- title:
--   Global degree-two bridge on the defect class equals the inflated cocycle
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes with $p\in S$, and a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w \mid \exists q\in S,\ q\in w\}$. Let $M$ be a $\mathbb Z/p$-linear representation of $\Gamma=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and let $F\subseteq\overline{\mathbb Q}$ be an intermediate field which is a number field, Galois over $\mathbb Q$, and unramified outside $S$ in the sense that $F/\mathbb Q$ is finite and, for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\Gamma$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup of $F$. Write $G=\mathrm{Gal}(F/\mathbb Q)$ and let $E=$ [`NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ`](def/NumberField_SUnitsModule.html#L52) be the $G$-representation on the $S_{\mathbb Q}$-units of $F$, written additively. Let $B$ be a finite $\mathbb Z[G]$-representation with $pB=0$, assume the three-term sequence [`Rep.homSeq₁ B E`](def/GroupCohomology_RelationHomDefect.html#L59) is short exact, let $\iota_E\colon E\to\mathrm{Additive}\,\overline{\mathbb Q}^\times$ be the map induced by the inclusion $F\hookrightarrow\overline{\mathbb Q}$ on units, and let $\kappa\colon B\to\mathrm{Hom}(M,\mathrm{Additive}\,\overline{\mathbb Q}^\times)$ be biadditive, equivariant in the sense $\kappa(\rho_B(\bar\gamma)b)(\rho_M(\gamma)m)=\gamma\cdot\kappa(b)(m)$ for the natural action on $\overline{\mathbb Q}^\times$ (with $\bar\gamma$ the restriction of $\gamma$ to $F$), and perfect in the sense that every additive $c\colon B\to\mathrm{Additive}\,\overline{\mathbb Q}^\times$ is $\kappa(\cdot)(m)$ for a unique $m\in M$. Let $\Lambda_E\colon H^1(G,\mathrm{Hom}(R(B),E))\to$ `continuousH2S S M`, the quotient of the $S$-level $2$-cocycles `levelCocyclesS₂ S M` by the $S$-level coboundaries, satisfy the predicate `IsGlobalBridge₂` for the restriction map $\Gamma\to G$, the presentation of $B$ given by [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15) and the relation-module inclusion [`Rep.relationModuleInt.ι B`](def/GroupCohomology_RelationModule.html#L75), the natural representation on $\overline{\mathbb Q}^\times$, $\iota_E$ and $\kappa$. Finally let $\eta\in H^1(G,$ [`Rep.defectQ B E`](def/GroupCohomology_RelationHomDefect.html#L55) $)$, where [`Rep.defectQ`](def/GroupCohomology_RelationHomDefect.html#L55) is the image subrepresentation of `preι B E`, let $c$ be a $2$-cocycle of $\mathrm{Hom}(B,E)$ whose class is the image of $\eta$ under the connecting map of [`Rep.homSeq₁ B E`](def/GroupCohomology_RelationHomDefect.html#L59) from degree $1$ to degree $2$, and let $m\colon\Gamma\times\Gamma\to M$ satisfy $\kappa(b)(m(\gamma_1,\gamma_2))=\iota_E\bigl(c(\bar\gamma_1,\bar\gamma_2)(b)\bigr)$ for all $\gamma_1,\gamma_2,b$ and lie in `levelCocyclesS₂ S M`. The conclusion is that $\Lambda_E$ applied to the image of $\eta$ under the degree-one map induced by the identity of $G$ and by the first morphism `(Rep.homSeq₂ B E).f` equals the class of $m$ in `continuousH2S S M`.
--
--   This is the compatibility statement identifying the global degree-two bridge, evaluated on a class coming from the relation-module defect representation, with the class in $S$-level continuous $H^2(\Gamma,M)$ of the $2$-cocycle obtained by reading the values of a representing $2$-cocycle for $\mathrm{Hom}(B,E)$ through the perfect pairing $\kappa$; both sides are coboundaries of the same lift, so the content is the comparison of the two constructions. It is used by [`NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq`](thm.html#NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq) and by [`NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero`](thm.html#NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_GroupCohomology_GlobalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (h1 : (Rep.homSeq₁ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).ShortExact)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (η : groupCohomology (Rep.defectQ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) 1)
    (c : cocycles₂ ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (hc : (H2π ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))).hom c = (groupCohomology.δ h1 1 2 rfl).hom η)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : ∀ (γ₁ γ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B), κ b (m (γ₁, γ₂)) =
      ιE (LinearMap.toAddMonoidHom ((c : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂)) b))
    (hmS : m ∈ levelCocyclesS₂ S M) :
    ΛE ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f 1).hom η) = continuousH2Sπ S M ⟨m, hmS⟩ := by sorry
