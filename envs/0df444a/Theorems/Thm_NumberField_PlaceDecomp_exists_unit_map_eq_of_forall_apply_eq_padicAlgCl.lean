-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_unit_map_eq_of_forall_apply_eq_padicAlgCl
-- name    : NumberField.PlaceDecomp.exists_unit_map_eq_of_forall_apply_eq_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/6d361044-45bb-560f-be97-10da84d881a0
-- title:
--   Units fixed by the kernel lie in Φ(F_w^×)
-- statement:
--   Let $q$ be a prime, let $F$ be an intermediate field of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` over $\mathbb Q$ which is a number field and Galois over $\mathbb Q$, and let $w$ be a height-one prime of $\mathcal O_F$. Let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ and let $\Phi$ be a ring homomorphism from the $w$-adic completion $F_w$ to the $q$-adic algebraically closed field `PadicAlgCl q`, subject to: (i) on $F$ one has $\Phi(\iota x)=(\mathtt{padicEmbedding }q)(\sigma x)$, where [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is the fixed $\mathbb Q$-embedding $\overline{\mathbb Q}\to$ `PadicAlgCl q` obtained by lifting into an algebraically closed field; (ii) for every $\tau\in\mathrm{Gal}(\mathtt{PadicAlgCl }q/\mathbb Q_q)$, the restriction to $F$ of $\sigma^{-1}\,(\mathtt{localGaloisToGlobal }q\,\tau)\,\sigma$ — where [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) sends $\tau$ to its restriction of scalars to $\mathbb Q$ followed by restriction to the normal subextension $\overline{\mathbb Q}$ — lies in `decomp ℚ ↥F w`, the decomposition subgroup in $\mathrm{Gal}(F/\mathbb Q)$ of the valuation subring of the $w$-adic valuation of $F$; (iii) every element $d$ of that decomposition subgroup is of this form for some $\tau$; (iv) whenever $d$ equals the restriction of $\sigma^{-1}(\mathtt{localGaloisToGlobal }q\,\tau)\sigma$, one has $\Phi(d\cdot x)=\tau(\Phi x)$ for all $x\in F_w$; and (v) $\Phi$ is continuous. Then for every unit $a$ of `PadicAlgCl q` fixed by all $\tau$ whose associated restriction to $F$ is the identity, there is a unit $x$ of $F_w$ with $\Phi(x)=a$.
--
--   This is the surjectivity half of the local compatibility ("local bridge") data at a finite place $w$: it identifies the units of the image $\Phi(F_w)$ with the units of `PadicAlgCl q` fixed by the subgroup of $\mathrm{Gal}(\mathtt{PadicAlgCl }q/\mathbb Q_q)$ acting trivially on $F$ through $\sigma$. It is used by [`NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl`](thm.html#NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl) and [`NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl`](thm.html#NumberField.PlaceDecomp.localBridge_hypotheses_padicAlgCl) when assembling the local–global comparison of Galois actions at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_unit_map_eq_of_forall_apply_eq_padicAlgCl.lean

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

theorem NumberField.PlaceDecomp.exists_unit_map_eq_of_forall_apply_eq_padicAlgCl
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
    ∀ a : (PadicAlgCl q)ˣ,
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) = 1 → τ (a : PadicAlgCl q) = a) →
      ∃ x : (w.adicCompletion ↥F)ˣ, Φ (x : w.adicCompletion ↥F) = a := by sorry
