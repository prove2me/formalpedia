-- Prove2me | Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
-- name    : NumberField.SUnits.isGlobalBridge2_apply_inflation_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1c06dbe6-4b5f-5aa8-bc74-12398c2aab97
-- title:
--   Inflation invariance of the global degree-two bridge Λ_E
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$, and a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w \mid \exists q \in S,\ q \in w\}$. Let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and let $F \le F'$ be intermediate fields of $\overline{\mathbb Q}/\mathbb Q$ that are number fields, Galois over $\mathbb Q$, and satisfy `IsUnramifiedOutside S`: finite-dimensional over $\mathbb Q$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in the fixing subgroup of the field. Let $\pi : \mathrm{Gal}(F'/\mathbb Q) \to \mathrm{Gal}(F/\mathbb Q)$ be a group homomorphism compatible with restriction of automorphisms of $\overline{\mathbb Q}$. Given short exact sequences $R \xrightarrow{f} P \xrightarrow{g} B$ of $\mathbb Z$-linear $\mathrm{Gal}(F/\mathbb Q)$-representations and $R' \xrightarrow{f'} P' \xrightarrow{g'} \mathrm{Res}_\pi B$ of $\mathrm{Gal}(F'/\mathbb Q)$-representations (injectivity, exactness, surjectivity hypothesised), with $P$, $P'$ finitely generated over $\mathbb Z$ and $B$ killed by $p$, together with $\rho_R : R' \to \mathrm{Res}_\pi R$ and $\rho_P : P' \to \mathrm{Res}_\pi P$ making a morphism of sequences over the identity of $B$ (that is, $f'$ followed by $\rho_P$ equals $\rho_R$ followed by $\mathrm{Res}_\pi f$, and $g' = \rho_P$ followed by $\mathrm{Res}_\pi g$). Let $\iota_E$, $\iota_{E'}$ be additive maps from the $S_{\mathbb Q}$-unit representations of $F$ and of $F'$ into $\mathrm{Additive}\,\overline{\mathbb Q}^\times$ given by the structural embeddings of $F$, $F'$ into $\overline{\mathbb Q}$, and $j_E : \mathrm{Res}_\pi(E_{F,S_{\mathbb Q}}) \to E_{F',S_{\mathbb Q}}$ a morphism with $\iota_{E'} \circ j_E = \iota_E$. Let $\kappa : B \to \mathrm{Hom}(M, \mathrm{Additive}\,\overline{\mathbb Q}^\times)$ be biadditive, equivariant for the Galois actions via restriction to $F$, and perfect in the sense that every additive $c : B \to \mathrm{Additive}\,\overline{\mathbb Q}^\times$ equals $\kappa(\cdot, m)$ for a unique $m \in M$. Finally let $\Lambda_E$ and $\Lambda_{E'}$ be additive maps from $H^1$ of the internal hom objects $\mathrm{Hom}(R, E_{F,S_{\mathbb Q}})$, respectively $\mathrm{Hom}(R', E_{F',S_{\mathbb Q}})$, to the group `continuousH2S S M` of level-$S$ degree-two cocycles modulo level-$S$ coboundaries, each satisfying the predicate `IsGlobalBridge₂` for the data at its own level (with $\kappa$ read on $\mathrm{Res}_\pi B$ at level $F'$). Then for $1$-cocycles $a$ at level $F$ and $a'$ at level $F'$ related by $a'(d')(x') = j_E\big(a(\pi d')(\rho_R x')\big)$ for all $d' \in \mathrm{Gal}(F'/\mathbb Q)$ and $x' \in R'$, the classes satisfy $\Lambda_{E'}[a'] = \Lambda_E[a]$.
--
--   This is the statement that the degree-two global duality bridge into $H^2$ of the $S$-ramified Galois cohomology of $M$ is unchanged by inflation along the tower of Galois levels unramified outside $S$, so that it factors through the colimit of the level-wise $\mathrm{Ext}^2$ groups in the sense of Milne's description of $\mathrm{Ext}^2_{G_S}(M^D, E_S)$ as $\varinjlim_F \mathrm{Ext}^2_{\mathrm{Gal}(F/\mathbb Q)}(M^D, E_{F,S})$. It is used in the construction of the Tate–Shafarevich pairing for the Galois cohomology groups involved in the level-raising and deformation arguments, in particular in the vanishing and nondegeneracy statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.isGlobalBridge2_apply_inflation_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F'] [IsGalois ℚ ↥F']
    (hFF' : F ≤ F') (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S)
    (π : (↥F' ≃ₐ[ℚ] ↥F') →* (↥F ≃ₐ[ℚ] ↥F))
    (hπ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F' σ) = AlgEquiv.restrictNormalHom ↥F σ)

    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {R' P' : Rep ℤ (↥F' ≃ₐ[ℚ] ↥F')} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res π B)
    (hf' : Function.Injective f'.hom) (hfg' : Function.Exact f'.hom g'.hom) (hg' : Function.Surjective g'.hom)
    [Module.Finite ℤ P] [Module.Finite ℤ P'] (hB : ∀ b : B, p • b = 0)
    (ρR : R' ⟶ Rep.res π R) (ρP : P' ⟶ Rep.res π P)
    (hρf : f' ≫ ρP = ρR ≫ (Rep.resFunctor π).map f) (hρg : g' = ρP ≫ (Rep.resFunctor π).map g)

    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (ιE' : NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE' : ∀ x, Additive.toMul (ιE' x) = Units.map (algebraMap ↥F' (AlgebraicClosure ℚ) : ↥F' →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F' Sℚ x))
    (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)
    (hjE : ∀ x, ιE' (jE.hom x) = ιE x)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {ΛE : H1 ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {ΛE' : H1 ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)) →+ continuousH2S S M}
    (hΛE' : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F') f' g' (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE'
      (show Rep.res π B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) ΛE')

    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (a' : cocycles₁ ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)))
    (ha' : ∀ (d' : (↥F' ≃ₐ[ℚ] ↥F')) (x' : R'),
      LinearMap.toAddMonoidHom ((a' : _ → _) d') x' = jE.hom (LinearMap.toAddMonoidHom ((a : _ → _) (π d')) (ρR.hom x'))) :
    ΛE' ((H1π _).hom a') = ΛE ((H1π _).hom a) := by sorry
