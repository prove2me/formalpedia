-- Prove2me | Theorems.Thm_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite
-- name    : NumberField.SUnits.locRes_isLocalBridge1_apply_eq_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1df5fb86-e120-5374-bc54-06647e282387
-- title:
--   Local–global compatibility of the degree-one bridges at q
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes and $q \in S$, and a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w : \exists\, \ell \in S,\ \ell \in w\}$. Let $M$ be a $\mathbb Z/p$-linear representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, let $F \subset \overline{\mathbb Q}$ be an intermediate field which is a number field and Galois over $\mathbb Q$, and let $w$ be a height-one prime of $\mathcal O_F$. The $q$-adic coordinates of $w$ are given by $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, a ring homomorphism $\Phi : F_w \to \overline{\mathbb Q}_q$ from the $w$-adic completion with $\Phi(x) = \iota_q(\sigma x)$ for $x \in F$ (where $\iota_q$ is the chosen embedding [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) of $\overline{\mathbb Q}$ into $\overline{\mathbb Q}_q$), and a homomorphism $\pi$ from $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ to the decomposition subgroup of $w$ in $\mathrm{Gal}(F/\mathbb Q)$ such that $\pi(\tau)$ acts on $F$ as the restriction of $\sigma^{-1}\,\mathrm{loc}_q(\tau)\,\sigma$, with $\mathrm{loc}_q$ the map $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q) \to \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ obtained by restricting scalars to $\mathbb Q$ and then restricting to $\overline{\mathbb Q}$, and such that $\Phi(\pi(\tau)\cdot x) = \tau(\Phi x)$ for all $x \in F_w$. Let $R \xrightarrow{f} P \xrightarrow{g} B$ be $\mathbb Z[\mathrm{Gal}(F/\mathbb Q)]$-representations with $f$ injective, the sequence exact at $P$, $g$ surjective, $P$ finite over $\mathbb Z$ and $p$ annihilating $B$. Let $\iota_E$ send the $S_{\mathbb Q}$-unit representation $E_{F,S}$ of $F$ into $\overline{\mathbb Q}^\times$ (written additively) by the structural inclusion of $F$ into $\overline{\mathbb Q}$, let $\kappa : B \times M \to \overline{\mathbb Q}^\times$ be biadditive, equivariant in the sense $\kappa(\gamma|_F \cdot b,\ \gamma \cdot m) = \gamma\,\kappa(b,m)$ for $\gamma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and perfect in the sense that every additive $c : B \to \overline{\mathbb Q}^\times$ is $\kappa(-,m)$ for a unique $m \in M$; let $\kappa_q : B \times M \to \overline{\mathbb Q}_q^\times$ be its $\sigma$-transport, $\kappa_q(b,m) = \iota_q(\sigma\,\kappa(b,\sigma^{-1}m))$. Assume $\Lambda_E$, an additive map from $\mathrm{Gal}(F/\mathbb Q)$-morphisms $R \to E_{F,S}$ to $H^1(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q), M)$, satisfies the predicate `IsLocalBridge₁` for the data $(\,\cdot\,|_F, f, g, \overline{\mathbb Q}^\times, \iota_E, \kappa)$, and that $\Lambda_q$, an additive map from morphisms $R \to F_w^\times$ of representations of the decomposition subgroup to $H^1(\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q), M)$, satisfies `IsLocalBridge₁` for the data obtained by restricting $f$ and $g$ to the decomposition subgroup, with $\pi$, $X = F_w^\times$, $A = \overline{\mathbb Q}_q^\times$, $\iota = \Phi$ on units, $M$ restricted along $\mathrm{loc}_q$, and $\kappa_q$. Then for every $\mathrm{Gal}(F/\mathbb Q)$-morphism $\varphi : R \to E_{F,S}$ and every morphism $\varphi_w : R \to F_w^\times$ of decomposition-subgroup representations whose values are the images of those of $\varphi$ under $F^\times \to F_w^\times$, the restriction map $H^1(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q), M) \to H^1(\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q), M)$ along the component of `extArithLoc S` indexed by $q$, namely $\mathrm{loc}_q$, carries $\Lambda_E(\varphi)$ to $\Lambda_q(\varphi_w)$.
--
--   This is the local–global compatibility, at the finite place above $q$, of the degree-one bridge maps that realise extension classes of the $S$-unit sequence as cohomology classes: localising the global class built from $\varphi$ gives the class built from the local component $\varphi_w$, in the style of the commuting square $\mathrm{Ext}^1(M^D, E_S) \to \mathrm{Ext}^1(M^D, J_S)$ over $H^1 \to P^1_S$. It feeds the assembly of local conditions at all places of $S$ together with the archimedean place, used in [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite.lean

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

theorem NumberField.SUnits.locRes_isLocalBridge1_apply_eq_of_finite
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
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
    {ΛE : (R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ H1 M}
    (hΛE : IsLocalBridge₁ (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M)}
    (hΛq : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (φ : R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)
    (φw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hφw : ∀ x : R, Additive.toMul (φw.hom x) =
      Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F) (NumberField.SUnits.val ℚ ↥F Sℚ (φ.hom x))) :
    (locRes (extArithLoc S) M (Sum.inr q)).hom (ΛE φ) = Λq φw := by sorry
