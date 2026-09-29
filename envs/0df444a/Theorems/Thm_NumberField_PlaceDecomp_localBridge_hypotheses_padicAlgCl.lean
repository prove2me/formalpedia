-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl
-- name    : NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/144bd7bf-97e5-5143-9f63-d37eebc83c5d
-- title:
--   Arithmetic hypotheses of the local bridge at a finite place
-- statement:
--   Fix a prime $q$, a subfield $F$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` which is a number field and Galois over $\mathbb Q$, a nonzero prime $w$ of $\mathcal O_F$, a $\mathbb Q$-automorphism $\sigma$ of $\overline{\mathbb Q}$, and a ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to `PadicAlgCl q`. Assume: $\Phi$ agrees on $F$ with $x \mapsto \iota_q(\sigma x)$, where $\iota_q =$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is the $\mathbb Q$-algebra embedding $\overline{\mathbb Q} \to$ `PadicAlgCl q` provided by algebraic closedness; for every $\tau \in \mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb Q_q)$ the restriction to $F$ of $\sigma^{-1}\,(\mathrm{localGaloisToGlobal}\,q\,\tau)\,\sigma$ lies in `decomp ℚ F w`, the decomposition subgroup of the valuation subring of $w$ inside $\mathrm{Gal}(F/\mathbb Q)$ — here [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) sends $\tau$ to the restriction to $\overline{\mathbb Q}$ of $\tau$ viewed as a $\mathbb Q$-algebra automorphism; every element of that decomposition subgroup arises so; whenever $d$ in the decomposition subgroup equals the restriction attached to $\tau$ one has $\Phi(d \cdot x) = \tau(\Phi x)$ for all $x \in F_w$; and $\Phi$ is continuous. The conclusion is the conjunction of three assertions. First, for all abelian groups $V, W$ with $W$ finitely generated free over $\mathbb Z$, every injective $f : V \to W$ and every homomorphism $\varphi : V \to F_w^\times$ (written additively), there is a homomorphism $\psi : W \to (\mathrm{PadicAlgCl}\,q)^\times$ with $\psi \circ f = \Phi \circ \varphi$ on units, and a finite extension $F_2/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\tau$ with [`localGaloisToGlobal q τ`](def/GaloisRep_CompletionBridge.html#L41) in the fixing subgroup of $F_2$ fixes all values of $\psi$, for the Galois action `Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)`. Second, any unit $a$ of $\mathrm{PadicAlgCl}\,q$ fixed by every $\tau$ whose associated restriction to $F$ is the identity lies in $\Phi((F_w)^\times)$. Third, for every finite type $\alpha$, every monoid homomorphism $\pi$ from $\mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb Q_q)$ to `decomp ℚ F w` given by the above restriction formula, and every $1$-cocycle $u$ of the representation $\mathrm{Hom}$ from the free $\mathbb Z[\mathrm{decomp}]$-module on $\alpha$ restricted along $\pi$ to $(\mathrm{PadicAlgCl}\,q)^\times$, if $u$ satisfies [`groupCohomology.IsLevelConstant₁ (localGaloisToGlobal q)`](def/GroupCohomology_ContinuousH2.html#L14) then $u$ is the image under $d_{01}$ of some $\chi$ in that representation which is fixed by all $\tau$ with [`localGaloisToGlobal q τ`](def/GaloisRep_CompletionBridge.html#L41) in the fixing subgroup of some finite extension $F_2/\mathbb Q$.
--
--   This packages, at a finite place $w$ of a Galois number field $F$, the three arithmetic inputs needed by the bridge between global idelic cocycles and $q$-adic coordinates: a divisible-lift statement with level control (extension of a homomorphism into $F_w^\times$ along an injection of abelian groups, with values in a finite layer), the identification of the fixed units of the kernel of the decomposition map with $\Phi((F_w)^\times)$, and a Hilbert 90 / Shapiro statement saying that level-constant $1$-cocycles with values in a coinduced unit module are coboundaries of level-fixed elements. It is used in the construction of classes in continuous $H^1$ and in the nondegeneracy of the dual-twist pairing on Selmer-type groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_localBridge_hypotheses_padicAlgCl.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (hsurj : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
    (heqv : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x))
    (hcont : Continuous Φ) :

    (∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.adicCompletion ↥F)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (PadicAlgCl q)ˣ,
        (∀ v : V, ψ (f v) = Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (φ v)))) ∧
        ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x : W, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (ψ x) = ψ x) ∧

    (∀ a : (PadicAlgCl q)ˣ,
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) = 1 → τ (a : PadicAlgCl q) = a) →
      ∃ x : (w.adicCompletion ↥F)ˣ, Φ (x : w.adicCompletion ↥F) = a) ∧

    (∀ (α : Type) [Finite α]
        (π : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
        (_ : ∀ τ, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
          AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))),
      groupCohomology.IsLevelConstant₁ (localGaloisToGlobal q)
        (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) →
      ∃ χ : (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (groupCohomology.d₀₁ _).hom χ = (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → _)) := by sorry
