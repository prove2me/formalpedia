-- Prove2me | Theorems.Thm_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite
-- name    : NumberField.SUnits.locRes2S_isGlobalBridge2_apply_eq_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c439db75-c600-5eb4-a9f4-8f6088f930d5
-- title:
--   Localisation of the degree-two global bridge at a finite place
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes containing $p$, and an element $q \in S$; let $S_{\mathbb Q}$ be a finite set of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w \mid \exists\, \ell \in S,\ \ell \in w\}$. Let $M$ be a representation of $\operatorname{Gal}(\bar{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and let $F \subseteq \bar{\mathbb Q}$ be a Galois number field over $\mathbb Q$ which is unramified outside $S$ in the sense that $F/\mathbb Q$ is finite and, for every prime $\ell \notin S$ and every valuation subring $A$ of $\bar{\mathbb Q}$ with $\ell$ a nonunit of $A$, the inertia subgroup of $A$ over $\mathbb Q$ fixes $F$ pointwise. Let $w$ be a height-one prime of $\mathcal O_F$, $\sigma$ an automorphism of $\bar{\mathbb Q}$ over $\mathbb Q$, and $\Phi$ a continuous ring homomorphism from the $w$-adic completion $F_w$ to an algebraic closure $\overline{\mathbb Q_q}$ of $\mathbb Q_q$ which on $F$ agrees with $\sigma$ followed by the fixed embedding [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17). Let $\pi$ be a homomorphism from $\operatorname{Gal}(\overline{\mathbb Q_q}/\mathbb Q_q)$ to the decomposition subgroup of $w$ in $\operatorname{Gal}(F/\mathbb Q)$ such that $\pi(\tau)$ is the restriction to $F$ of $\sigma^{-1}\,\iota_q(\tau)\,\sigma$, where $\iota_q =$ `primeLocalToGlobal q` is the local-to-global map, and such that $\Phi$ is equivariant: $\Phi(\pi(\tau) \cdot x) = \tau(\Phi(x))$. Let $R \xrightarrow{f} P \xrightarrow{g} B$ be maps of $\mathbb Z[\operatorname{Gal}(F/\mathbb Q)]$-representations with $f$ injective, the sequence exact at $P$, $g$ surjective, $P$ finite over $\mathbb Z$ and $B$ killed by $p$. Let $\iota_E$ send the $S_{\mathbb Q}$-unit representation of $F$ into $\bar{\mathbb Q}^\times$ (written additively) via the inclusion $F^\times \hookrightarrow \bar{\mathbb Q}^\times$, let $\kappa \colon B \times M \to \bar{\mathbb Q}^\times$ be a biadditive pairing which is Galois-equivariant for the restriction map $\operatorname{Gal}(\bar{\mathbb Q}/\mathbb Q) \to \operatorname{Gal}(F/\mathbb Q)$ and identifies $M$ with the full additive dual of $B$ in $\bar{\mathbb Q}^\times$ (every additive $c \colon B \to \bar{\mathbb Q}^\times$ is $\kappa(\cdot, m)$ for a unique $m$), and let $\kappa_q \colon B \times M \to \overline{\mathbb Q_q}^\times$ be its $\sigma$-twisted push-forward, $\kappa_q(b,m) = \iota_{p\text{-adic}}\bigl(\sigma\,\kappa(b, \sigma^{-1}m)\bigr)$. Let $\Lambda_E$ from $H^1$ of the internal hom $\underline{\operatorname{Hom}}(R, E_{F,S})$ to the $S$-level continuous $H^2$ of $M$ satisfy the predicate `IsGlobalBridge₂` for the data $(f, g, \iota_E, \kappa)$ with $A$ the representation of $\operatorname{Gal}(\bar{\mathbb Q}/\mathbb Q)$ on $\bar{\mathbb Q}^\times$, and let $\Lambda_q$ from $H^1$ of $\underline{\operatorname{Hom}}(R, F_w^\times)$ over the decomposition group to the continuous $H^2$ of $M$ along $\iota_q$ satisfy `IsLocalBridge₂` for $\pi$, the restrictions of $f$ and $g$ to the decomposition group, $A$ the representation on $\overline{\mathbb Q_q}^\times$, the map induced by $\Phi$ on units, and $\kappa_q$. Finally let $a$ be a $1$-cocycle valued in $\underline{\operatorname{Hom}}(R, E_{F,S})$ and $a_w$ a $1$-cocycle of the decomposition group valued in $\underline{\operatorname{Hom}}(R, F_w^\times)$ such that for every $d$ in the decomposition group and every $x \in R$ the unit $a_w(d)(x)$ is the image in $F_w^\times$ of the $S_{\mathbb Q}$-unit $a(d)(x)$. The conclusion is that `locRes₂S`, the localisation map along `extArithLoc S (Sum.inr q)` $= \iota_q$ on $S$-level continuous $H^2$, carries the class $\Lambda_E([a])$ to $\Lambda_q([a_w])$.
--
--   This is the degree-two local–global compatibility square for the Tate-duality bridges: the global $\mathrm{Ext}^2$-style bridge built from $S$-units, localised at the finite place $q$, agrees with the local bridge built from the $w$-adic completion, on classes represented by compatible pairs of $1$-cocycles. It feeds the construction of the $P^2$-row of the Poitou–Tate sequence and is cited in the proof that the pairing on $Ш^1$ against the dual twist of $Ш^2$ is nondegenerate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.lean

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

theorem NumberField.SUnits.locRes2S_isGlobalBridge2_apply_eq_of_finite
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) (hpS : pPrime p ∈ S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκq : ∀ (b : B) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))
    {ΛE : H1 ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {Λq : H1 ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) →+
        continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)}
    (hΛq : IsLocalBridge₂ (primeLocalToGlobal q) π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (aw : cocycles₁ ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)))
    (haw : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : R),
      Additive.toMul (LinearMap.toAddMonoidHom ((aw : _ → _) d) x) =
        Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F)
          (NumberField.SUnits.val ℚ ↥F Sℚ (LinearMap.toAddMonoidHom ((a : _ → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x))) :
    locRes₂S S M (extArithLoc S (Sum.inr q)) (ΛE ((H1π _).hom a)) = Λq ((H1π _).hom aw) := by sorry
