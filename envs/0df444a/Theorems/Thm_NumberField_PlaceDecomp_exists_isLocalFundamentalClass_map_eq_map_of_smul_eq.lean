-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
-- name    : NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/35269007-9d26-52de-b693-6df7dd016e8d
-- title:
--   Transport of a local fundamental class along σ
-- statement:
--   Let $E\subseteq F$ be number fields with $F/E$ Galois, let $w,w_1$ be height-one primes of $\mathcal O_F$ and let $\sigma\in\operatorname{Gal}(F/E)$ satisfy $\sigma\cdot w=w_1$; write $D_w$ for [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation, and similarly $D_{w_1}$. Assume given a monoid homomorphism $c\colon D_{w_1}\to D_w$ with $c(\tau)=\sigma^{-1}\tau\sigma$, and a morphism $T$ of $\mathbb Z$-representations of $D_{w_1}$ from the restriction along $c$ of $(F_w)^\times$ to $(F_{w_1})^\times$ whose underlying map on units is the ring isomorphism $F_w\cong F_{w_1}$ transported along $\sigma$. Let $q$ be a prime, $L'$ a finite extension of $\mathbb Q_q$ inside a fixed algebraic closure carrying an action of $D_w$ by semiring automorphisms, compatible with an action on $(L')^\times$, and let $\Phi\colon F_w\xrightarrow{\sim}L'$ be a ring isomorphism, with the hypotheses that $D_w$ fixes the image of $\mathbb Q_q$, that the unit action is induced by the field action, and that $\Phi$ is $D_w$-equivariant. Let $K_0$ be a finite extension of $\mathbb Q_q$ with $K_0\le L'$ such that an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$; let $\theta$ be the morphism of $D_w$-representations $(L')^\times\to (F_w)^\times$ induced by $\Phi^{-1}$, and let $u\in H^2(D_w,(L')^\times)$ satisfy the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60): for every finite over-layer $M\supseteq L'$ with a finite group $H$ acting faithfully, normal subgroups $N_L,N_n\trianglelefteq H$, an isomorphism $e\colon D_w\cong H/N_L$, an element $\varphi$ and a unit $\pi$ forming an unramified overlayer datum over $K_0$, and every morphism $\iota$ from the restriction of $(L')^\times$ along $e^{-1}\circ\mathrm{pr}$ to $(M)^\times$ lifting the inclusion on units, the image of $u$ under $H^2(e^{-1}\circ\mathrm{pr},\iota)$ is the inflation from $H/N_n$ of the class of the cyclic carry cochain built from $\varphi$ and $\pi$. The conclusion is that $\#D_{w_1}=\#D_w$ and that there exist actions of $D_{w_1}$ on $L'$ and on $(L')^\times$, a ring isomorphism $\Phi_1\colon F_{w_1}\xrightarrow{\sim}L'$, a morphism $\theta_1$ of $D_{w_1}$-representations $(L')^\times\to (F_{w_1})^\times$ and a class $u_1\in H^2(D_{w_1},(L')^\times)$ satisfying the same list of conditions with $D_{w_1},\Phi_1,\theta_1,u_1$ in place of $D_w,\Phi,\theta,u$ (triviality on $\mathbb Q_q$, compatibility of the unit action, equivariance of $\Phi_1$, the base property of $K_0$, $\theta_1$ induced by $\Phi_1^{-1}$, and `IsLocalFundamentalClass` for $u_1$), and such that $H^2(c,T)$ applied to $H^2(\mathrm{id},\theta)(u)$ equals $H^2(\mathrm{id},\theta_1)(u_1)$ in $H^2(D_{w_1},(F_{w_1})^\times)$.
--
--   This is the transport-of-structure statement for local fundamental classes under conjugation: the data attached to a place $w$ and its local class move along $\sigma$ to the conjugate place $w_1=\sigma w$, compatibly with the induced map on $H^2$ of the unit groups of the completions. It is used in the Herbrand-quotient computations over a Galois orbit of places, where classes at different places above a given place of $E$ must be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)

    (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
    (Φ : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : w.adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
    ∃ (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) L')
      (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)
      (Φ₁ : w₁.adicCompletion F ≃+* L')
      (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
      (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (↥L')ˣ)),
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L')) ∧
      (∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w₁)) (y : w₁.adicCompletion F), Φ₁ (g • y) = g • Φ₁ y) ∧
      ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ ∧
      (∀ y : (↥L')ˣ, ((Additive.toMul (θ₁.hom (Additive.ofMul y)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) = Φ₁.symm (y : L')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w₁)) K₀ u₁ ∧
      (groupCohomology.map c T 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u) =
        (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w₁)) θ₁ 2).hom u₁ := by sorry
