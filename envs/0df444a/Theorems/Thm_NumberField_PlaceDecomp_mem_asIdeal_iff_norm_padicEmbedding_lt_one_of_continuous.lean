-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
-- name    : NumberField.PlaceDecomp.mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/869cd9c4-18da-5fff-87e3-37d749e26b5f
-- title:
--   A continuous q-adic embedding of F_w recovers w
-- statement:
--   Let $q$ be a prime and let $F$ be an intermediate field of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (the Mathlib algebraic closure `AlgebraicClosure ℚ`) which is a number field and Galois over $\mathbb{Q}$. Let $w$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_F$, with associated prime ideal `w.asIdeal` and $w$-adic completion $F_w$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$. Write [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) for the $\mathbb{Q}$-algebra embedding $\overline{\mathbb{Q}} \to$ `PadicAlgCl q` obtained by lifting along algebraic closedness of the target. Suppose given a ring homomorphism $\Phi \colon F_w \to$ `PadicAlgCl q` such that for every $x \in F$ one has $\Phi(x) =$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) $(\sigma(x))$, where $x$ is viewed in $F_w$ through the structure map and in $\overline{\mathbb{Q}}$ through the inclusion of $F$, and suppose $\Phi$ is continuous. Then for every $x \in \mathcal{O}_F$ one has $x \in$ `w.asIdeal` if and only if $\|$[`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17)$(\sigma(x))\| < 1$.
--
--   This is the standard fact that a continuous embedding of a completion $F_w$ into an algebraically closed complete field of residue characteristic $q$ pins down the place $w$: the prime of $\mathcal{O}_F$ it induces is exactly $\mathfrak{p}_w$, detected by the absolute value being $<1$. It is used in the construction of local restrictions of Galois representations at the finite places, where the $q$-adic coordinates of a global cocycle must be matched with a prescribed place $w$ of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous.lean

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

theorem NumberField.PlaceDecomp.mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ) :
    ∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := by sorry
