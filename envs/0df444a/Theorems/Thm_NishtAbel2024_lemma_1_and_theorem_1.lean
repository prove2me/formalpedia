-- Prove2me | Theorems.Thm_NishtAbel2024_lemma_1_and_theorem_1
-- name    : NishtAbel2024.lemma_1_and_theorem_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T19:03:59.946634+00:00
-- url     : https://prove2.me/theorems/656435ad-65dc-4245-a9b6-bcaad4693b51
-- title:
--   Compatibility of Invocation Graph Composition (Lemma 1 & Corollary) and Well-Foundedness of SCT_G (Theorem 1)
-- statement:
--   Lemma 1, Corollary, and Theorem 1 (Section 5.3, pp. 34–35): (1) compatibility of invocation graph composition `G₁ ∘ G₂` with graph conformance `ConformsToGraph` over any compatible strict/weak orders; (2) compatibility of iterated composition `G₁ ∘ ⋯ ∘ Gₙ` across finite ordinal chains; and (3) well-foundedness of the semantic call relation `SCTCallRel 𝒢` whenever `SCTValid 𝒢` holds.
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Section 5.3, Lemma 1, Corollary, and Theorem 1 (pp. 34–35).

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

/-- Lemma 1 (Soundness of composition, p. 34), Corollary (Collapsing of finite chains, p. 34),
and Theorem 1 (Soundness of `G`, pp. 34–35):
1. (**Lemma 1**) For any type `S` equipped with transitive relations `ltRel, leRel : S → S → Prop`
   such that `ltRel` implies `leRel` and `ltRel`/`leRel` compose transitively into `ltRel`, if
   `a⃗ ≺_{G₁} b⃗` and `b⃗ ≺_{G₂} c⃗`, then `a⃗ ≺_{G₁ ∘ G₂} c⃗`.
2. (**Corollary**) For any non-empty chain of invocation graphs `G₁ :: Gs` and ordinal tuples
   `s₀ :: s₁ :: ... :: sₙ` of matching length `(G₁ :: Gs).length + 1` where each adjacent step
   satisfies `OrdConformsToGraph`, the endpoints conform to `Gs.foldl InvGraph.comp G₁`.
3. (**Theorem 1**) If `⊢ 𝒢` (`SCTValid 𝒢`), then `SCT_𝒢` (`SCTCallRel 𝒢`) is well-founded. -/
theorem lemma_1_and_theorem_1 :
    (∀ {S : Type} (ltRel leRel : S → S → Prop),
      (∀ x y, ltRel x y → leRel x y) →
      (∀ x y z, leRel x y → leRel y z → leRel x z) →
      (∀ x y z, ltRel x y → leRel y z → ltRel x z) →
      (∀ x y z, leRel x y → ltRel y z → ltRel x z) →
      ∀ (G₁ G₂ : InvGraph) (a b c : List S),
        ConformsToGraph ltRel leRel G₁ a b →
        ConformsToGraph ltRel leRel G₂ b c →
        ConformsToGraph ltRel leRel (G₁.comp G₂) a c) ∧
    (∀ (G₁ : InvGraph) (Gs : List InvGraph) (s₀ sₙ : List SizeOrd) (mid : List (List SizeOrd)),
      let graphs := G₁ :: Gs
      let chain := [s₀] ++ mid ++ [sₙ]
      mid.length = Gs.length →
      (∀ (k : Nat) (hk : k < graphs.length)
         (hk1 : k < chain.length) (hk2 : k + 1 < chain.length),
        OrdConformsToGraph (graphs.get ⟨k, hk⟩) (chain.get ⟨k, hk1⟩) (chain.get ⟨k + 1, hk2⟩)) →
      OrdConformsToGraph (Gs.foldl InvGraph.comp G₁) s₀ sₙ) ∧
    (∀ 𝒢 : InvGraphFamily,
      SCTValid 𝒢 →
      WellFounded (SCTCallRel 𝒢)) := by
  sorry

end NishtAbel2024
