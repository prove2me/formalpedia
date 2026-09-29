-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_extension_fixed_of_injective_padicAlgCl
-- name    : NumberField.PlaceDecomp.exists_extension_fixed_of_injective_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/217de0b4-91b0-508e-8718-1d922b012162
-- title:
--   Divisible lift to ℚ̄_q^× fixed by a finite global level
-- statement:
--   Fix a prime $q$ and an intermediate field $F$ of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ which is a number field and Galois over $\mathbb{Q}$, a height-one prime $w$ of $\mathcal{O}_F$, an automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $\mathbb{Q}$, and a ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to $\mathrm{PadicAlgCl}\ q$. Assume: on $F$, $\Phi$ agrees with $\tau\mapsto$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) applied to $\sigma$, where [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is the $\mathbb{Q}$-algebra embedding of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ into $\mathrm{PadicAlgCl}\ q$ furnished by algebraic closedness; for every $\tau \in \mathrm{Gal}(\mathrm{PadicAlgCl}\ q/\mathbb{Q}_q)$ the restriction to $F$ of $\sigma^{-1}\cdot(\mathrm{localGaloisToGlobal}\ q\ \tau)\cdot\sigma$ lies in `decomp ℚ F w`, the decomposition subgroup of the valuation subring of the $w$-adic valuation of $F$ inside $\mathrm{Gal}(F/\mathbb{Q})$, where [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) sends $\tau$ to the restriction of $\tau$, viewed $\mathbb{Q}$-linearly, to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$; every element of `decomp ℚ F w` is of this shape; whenever $d$ in that decomposition subgroup equals the restriction of $\sigma^{-1}\cdot(\mathrm{localGaloisToGlobal}\ q\ \tau)\cdot\sigma$ one has $\Phi(d\cdot x)=\tau(\Phi x)$ for all $x\in F_w$; and $\Phi$ is continuous. The conclusion asserts: for all abelian groups $V$ and $W$ with $W$ free and finitely generated over $\mathbb{Z}$, every injective $\mathbb{Z}$-linear $f\colon V\to W$ and every $\mathbb{Z}$-linear $\varphi\colon V\to \mathrm{Additive}\ F_w^{\times}$, there is a $\mathbb{Z}$-linear $\psi\colon W\to \mathrm{Additive}\ (\mathrm{PadicAlgCl}\ q)^{\times}$ with $\psi(f v)$ equal to the image of $\varphi(v)$ under the map on unit groups induced by $\Phi$, for all $v\in V$, together with an intermediate field $F_2$ of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\tau$ whose image under [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) lies in the fixing subgroup of $F_2$ acts trivially on each $\psi(x)$, $x\in W$, for the action of $\mathrm{Gal}(\mathrm{PadicAlgCl}\ q/\mathbb{Q}_q)$ on $\mathrm{Additive}\ (\mathrm{PadicAlgCl}\ q)^{\times}$ given by `Rep.ofAlgebraAutOnUnits`.
--
--   This is the extension-and-finite-level statement that serves as the first of the hypotheses packaged by [`NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl`](thm.html#NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl), and it is also used by [`NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl`](thm.html#NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl); the $q$-adic coordinates at the finite place $w$ are fixed by $\sigma$ and $\Phi$ as in the hypotheses, and the output $\psi$ is required to be defined over a finite global level $F_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_extension_fixed_of_injective_padicAlgCl.lean

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

theorem NumberField.PlaceDecomp.exists_extension_fixed_of_injective_padicAlgCl
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
    ∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.adicCompletion ↥F)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (PadicAlgCl q)ˣ,
        (∀ v : V, ψ (f v) = Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (φ v)))) ∧
        ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x : W, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (ψ x) = ψ x := by sorry
