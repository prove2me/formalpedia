-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
-- name    : NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/be4e2a0e-9ee9-58a7-87a9-23e59c51723c
-- title:
--   q-adic coordinates for a completion at a finite place
-- statement:
--   Let $q$ be a prime, let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a number field and Galois over $\mathbb{Q}$, and let $w$ be a height-one prime of $\mathcal{O}_F$ containing the image of $q$, i.e. a finite place of $F$ above $q$. The assertion is the existence of a $\mathbb{Q}$-automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and a ring homomorphism $\Phi \colon F_w \to \overline{\mathbb{Q}}_q$ (where $F_w$ is the $w$-adic completion and $\overline{\mathbb{Q}}_q =$ `PadicAlgCl q`) with the following four properties together with continuity of $\Phi$. First, on $F$ the map $\Phi$ agrees with $\iota_q \circ \sigma$, where $\iota_q =$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is the $\mathbb{Q}$-algebra map $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$ obtained by lifting into an algebraically closed field. Second, for every $\tau \in \mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$, the restriction to $F$ of $\sigma^{-1}\,(\mathrm{localGaloisToGlobal}\ q\ \tau)\,\sigma$ — where [`localGaloisToGlobal`](def/GaloisRep_CompletionBridge.html#L41) sends $\tau$ to the restriction of $\tau$, viewed as a $\mathbb{Q}$-automorphism, to the normal subextension $\overline{\mathbb{Q}}$ — lies in `decomp ℚ F w`, the subgroup of $F \simeq_{\mathbb{Q}} F$ preserving the valuation subring of the $w$-adic valuation. Third, conversely, every element $d$ of that subgroup is of this form for some $\tau$. Fourth, whenever $d$ and $\tau$ are so related, $\Phi(d \cdot x) = \tau(\Phi(x))$ for all $x \in F_w$, the action of $d$ on $F_w$ being the one induced on the completion.
--
--   This is the statement that the decomposition group at $w$ is the Galois group of the completion $F_w$, rendered in coordinates pinned to a fixed embedding $\iota_q \colon \overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$: the auxiliary automorphism $\sigma$ carries $w$ to the place cut out by $\iota_q$, so that the statement is available at an arbitrary finite place above $q$ rather than at a preferred one. It is used in the treatment of local restriction maps on Kummer classes and on continuous $H^1$, where local and global Galois actions must be compared through $\iota_q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding.lean

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

theorem NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (hw : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal) :
    ∃ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q),
      (∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ))) ∧
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w) ∧
      (∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ)) ∧
      (∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
        ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x)) ∧
      Continuous Φ := by sorry
