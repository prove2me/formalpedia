-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
-- name    : NumberField.PlaceDecomp.exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/291819ba-276a-5520-93c5-d73d51545081
-- title:
--   Level-constant cocycles into ℚ̄_q^× are level-fixed coboundaries
-- statement:
--   Fix a prime $q$ and an intermediate field $F$ of $\mathbb Q$ in $\mathrm{AlgebraicClosure}\,\mathbb Q$ which is a number field and Galois over $\mathbb Q$, together with a prime $w$ of $\mathcal O_F$, an automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\,\mathbb Q$ over $\mathbb Q$, and a ring homomorphism $\Phi$ from the $w$-adic completion of $F$ to $\mathrm{PadicAlgCl}\,q$ such that: $\Phi$ agrees on $F$ with $\tau \mapsto \mathrm{padicEmbedding}\,q(\sigma(\cdot))$, i.e. with the fixed $\mathbb Q$-embedding of $\mathrm{AlgebraicClosure}\,\mathbb Q$ into $\mathrm{PadicAlgCl}\,q$ precomposed with $\sigma$ ($h\Phi F$); for every $\tau \in \mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb Q_q)$ the restriction to $F$ of $\sigma^{-1}\,(\mathrm{localGaloisToGlobal}\,q\,\tau)\,\sigma$ lies in $\mathrm{decomp}\,\mathbb Q\,F\,w$, the decomposition subgroup of the valuation subring of the $w$-adic valuation inside $\mathrm{Gal}(F/\mathbb Q)$ (`hmem`), and every element of that decomposition subgroup arises this way (`hsurj`); whenever $d$ in the decomposition subgroup is so represented by $\tau$, one has $\Phi(d \bullet x) = \tau(\Phi x)$ for all $x$ in the completion (`heqv`); and $\Phi$ is continuous. Here $\mathrm{localGaloisToGlobal}\,q$ sends $\tau$ to the restriction of its underlying $\mathbb Q$-algebra automorphism to $\mathrm{AlgebraicClosure}\,\mathbb Q$. The conclusion asserts, for every finite type $\alpha$, every monoid homomorphism $\pi$ from $\mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb Q_q)$ to $\mathrm{decomp}\,\mathbb Q\,F\,w$ whose underlying map is $\tau \mapsto$ the restriction to $F$ of $\sigma^{-1}(\mathrm{localGaloisToGlobal}\,q\,\tau)\sigma$, and every $1$-cocycle $u$ of $\mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb Q_q)$ with values in the internal hom from the free representation $\mathbb Z[\mathrm{decomp}\,\mathbb Q\,F\,w]^{(\alpha)}$, restricted along $\pi$, into $\mathrm{PadicAlgCl}(q)^\times$ with its Galois action, the following: if $u$ satisfies the predicate [`groupCohomology.IsLevelConstant₁`](def/GroupCohomology_ContinuousH2.html#L14) relative to $\mathrm{localGaloisToGlobal}\,q$ (a finite-level condition which, by [`groupCohomology.exists_isGalois_of_isLevelConstant1`](thm.html#groupCohomology.exists_isGalois_of_isLevelConstant1), provides a finite Galois $F_1/\mathbb Q$ with $u(g s) = u(g) = u(s g)$ whenever $\mathrm{localGaloisToGlobal}\,q\,s$ fixes $F_1$), then there is an element $\chi$ of that internal hom which is itself of finite level — there is a finite extension $F_2/\mathbb Q$ inside $\mathrm{AlgebraicClosure}\,\mathbb Q$ such that every $\tau$ with $\mathrm{localGaloisToGlobal}\,q\,\tau$ in the fixing subgroup of $F_2$ satisfies $\rho(\tau)(\chi(x)) = \chi(x)$ for all $x$ — and whose image under the degree-$0$ to degree-$1$ differential $\mathrm{d}_{01}$ is the function underlying $u$.
--
--   This is a Hilbert-theorem-90 statement in the $q$-adic coordinates attached to a finite place $w$: the level-constant first cohomology of $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ with coefficients in $\mathrm{Hom}(\mathbb Z[D_w]^{(\alpha)}, \overline{\mathbb Q}_q^{\times})$ vanishes, with a witness that is itself fixed by the Galois group of a finite level. It serves as one conjunct of the local-bridge hypotheses, and is cited by [`NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl`](thm.html#NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl) and [`NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl`](thm.html#NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl.lean

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

theorem NumberField.PlaceDecomp.exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
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
    ∀ (α : Type) [Finite α]
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
        (groupCohomology.d₀₁ _).hom χ = (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → _) := by sorry
