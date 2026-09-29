-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
-- name    : NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c4300653-a367-5f79-9003-5fb5ed18ccb3
-- title:
--   q-adic coordinates of F_w for a prescribed σ
-- statement:
--   Let $q$ be a prime, let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a number field and Galois over $\mathbb{Q}$, let $w$ be a nonzero prime of the ring of integers $\mathcal{O}_F$ (a point of the height-one spectrum), and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$. Write $\iota_q =$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) for the $\mathbb{Q}$-algebra map $\overline{\mathbb{Q}} \to$ `PadicAlgCl q` obtained by lifting into an algebraically closed field, and [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) for the homomorphism sending $\tau \in \mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb{Q}_q)$ to the restriction of $\tau$, viewed as a $\mathbb{Q}$-algebra automorphism, to the normal subextension $\overline{\mathbb{Q}}$. Assume that $\iota_q \circ \sigma$ cuts out $w$: for every $x \in \mathcal{O}_F$ one has $x \in w$ if and only if $\|\iota_q(\sigma(x))\| < 1$. Then there exists a ring homomorphism $\Phi$ from the adic completion $F_w$ of $F$ at $w$ to `PadicAlgCl q` such that: (i) $\Phi$ composed with the structure map $F \to F_w$ equals $x \mapsto \iota_q(\sigma(x))$; (ii) for every $\tau \in \mathrm{Gal}(\mathrm{PadicAlgCl}\,q/\mathbb{Q}_q)$, the restriction to $F$ of the conjugate $\sigma^{-1}\,(\mathrm{localGaloisToGlobal}\,q\,\tau)\,\sigma$ lies in [`NumberField.PlaceDecomp.decomp ℚ F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation of $F$ inside $\mathrm{Gal}(F/\mathbb{Q})$; (iii) conversely every element $d$ of that decomposition subgroup is of this form for some $\tau$; (iv) whenever $d$ in the decomposition subgroup equals the restriction of $\sigma^{-1}\,(\mathrm{localGaloisToGlobal}\,q\,\tau)\,\sigma$, one has $\Phi(d \cdot x) = \tau(\Phi(x))$ for all $x \in F_w$, where $\cdot$ is the action of the decomposition subgroup on $F_w$; and (v) $\Phi$ is continuous.
--
--   This is the standard identification of the completion $F_w$ with the $w$-adic coordinates of a $q$-adic embedding: a continuous embedding $F_w \to \overline{\mathbb{Q}}_q$ extending the given embedding $\iota_q \circ \sigma$ of $F$, under which the decomposition group at $w$ is exactly the image of the local Galois group and the action on $F_w$ matches the local Galois action. It is the variant in which $\sigma$ is prescribed by the condition that $\iota_q \circ \sigma$ cuts out $w$, rather than produced existentially from $q \in w$, and it feeds the computation of local restriction maps in continuous $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff.lean

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

theorem NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1) :
    ∃ Φ : w.adicCompletion ↥F →+* PadicAlgCl q,
      (∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ))) ∧
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w) ∧
      (∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ)) ∧
      (∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
        ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x)) ∧
      Continuous Φ := by sorry
