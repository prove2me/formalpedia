-- Prove2me | Theorems.Thm_NumberField_SUnits_isLocalBridge1_apply_mem_continuousH1S
-- name    : NumberField.SUnits.isLocalBridge1_apply_mem_continuousH1S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/715b1749-cb0d-523b-bea8-8375d92c8a7d
-- title:
--   Local-bridge classes of S-units lie in continuousH1S
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$ (as the element `pPrime p` of `Nat.Primes`), together with a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w \mid \exists\, q\in S,\ q\in w\}$. Let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and let $F\subset\overline{\mathbb Q}$ be an intermediate field which is a number field, Galois over $\mathbb Q$, and satisfies `IsUnramifiedOutside S`: $F/\mathbb Q$ is finite and, for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ fixes $F$ pointwise. Let $R\xrightarrow{f}P\xrightarrow{g}B$ be morphisms of $\mathbb Z[\mathrm{Gal}(F/\mathbb Q)]$-representations with $f$ injective, $g$ surjective, the pair exact at $P$, with $P$ finite over $\mathbb Z$ and $p\cdot B=0$. Let $\iota_E$ be an additive map from the $S$-unit representation `sUnitsRep ℚ F Sℚ` (the $\mathbb Z$-subrepresentation of $\mathrm{Additive}\,F^\times$ cut out by the $S$-units) into $\mathrm{Additive}\,\overline{\mathbb Q}^\times$ which, multiplicatively, is the map induced by $F\hookrightarrow\overline{\mathbb Q}$ on underlying units. Let $\kappa$ be a biadditive pairing $B\times M\to\mathrm{Additive}\,\overline{\mathbb Q}^\times$ which is equivariant in the sense that $\kappa(\rho_B(\gamma|_F)b,\ \rho_M(\gamma)m)=\gamma\cdot\kappa(b,m)$ for all $\gamma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and perfect in the sense that every additive homomorphism $B\to\mathrm{Additive}\,\overline{\mathbb Q}^\times$ is $\kappa(\cdot,m)$ for a unique $m\in M$. Finally let $\Lambda$ be an additive map from $\mathrm{Hom}_{\mathrm{Gal}(F/\mathbb Q)}(R,\,\text{$S$-units})$ to $H^1(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q),M)$ satisfying the predicate `IsLocalBridge₁` relative to the restriction map $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{Gal}(F/\mathbb Q)$, the data $f,g,\iota_E,\kappa$ and the representation $\overline{\mathbb Q}^\times$. Then for every equivariant $\varphi:R\to\text{$S$-units}$, the class $\Lambda\varphi$ lies in `continuousH1S S M`, the image under the projection `H1π M` of the submodule `levelCocyclesS₁ S M` of $1$-cocycles.
--
--   This is the degree-one comparison, at a finite level $F$, between $S$-unit-valued homomorphisms and Galois cohomology classes that are unramified outside $S$, in the form needed for the Tate-duality identification $\mathrm{Ext}^1(M^D,E_{F,S})\cong H^1(G_S,M)$: the classes produced by a local bridge automatically satisfy the $S$-level condition defining `continuousH1S`. It is used by [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two), and rests on the Kummer-theoretic fact that adjoining a $p$-th root of an $S$-unit to an $S$-level field again gives a field unramified outside $S$ when $p\in S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_isLocalBridge1_apply_mem_continuousH1S.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.isLocalBridge1_apply_mem_continuousH1S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {Λ : (R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ H1 M}
    (hΛ : IsLocalBridge₁ (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ Λ)
    (φ : R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    Λ φ ∈ continuousH1S S M := by sorry
