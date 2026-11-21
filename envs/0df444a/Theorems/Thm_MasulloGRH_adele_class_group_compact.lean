-- Prove2me | Theorems.Thm_MasulloGRH_adele_class_group_compact
-- name    : MasulloGRH.adele_class_group_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:35:11.462119+00:00
-- url     : https://prove2.me/theorems/f118b17c-b69d-405a-a21c-de4561523fe5
-- title:
--   Lemma A.1.2.1 — $F$ is discrete in $\mathbb A_F$ and $\mathbb A_F/F$ is compact
-- statement:
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring and $\iota\colon F\to\mathbb A_F$ the diagonal embedding.
--
--   1. $\iota$ is a closed map when $F$ carries the discrete topology: the image of every subset of $F$ is closed in $\mathbb A_F$.
--   2. The image $\iota(F)$ is discrete in $\mathbb A_F$.
--   3. The quotient $\mathbb A_F/F$ is compact and Hausdorff.
--   4. $\mathbb A_F/F$ is uniquely divisible: for every integer $n\ge1$, multiplication by $n$ is a bijection of $\mathbb A_F/F$.
--   5. Let $\mathbb A_{F,S_\infty}\times\widehat{\mathcal O}_F\subset\mathbb A_F$ be the adeles that are integral at every finite place. The map
--   $$(\mathbb A_{F,S_\infty}\times\widehat{\mathcal O}_F)/\mathcal O_F\longrightarrow\mathbb A_F/F$$
--   is an isomorphism of topological groups: every adele is the sum of an integral adele and an element of $F$; an element of $F$ is an integral adele exactly when it lies in $\mathcal O_F$; and the image in $\mathbb A_F/F$ of every relatively open subset of the integral adeles is open.
--
--   This is the additive compactness statement on which the Tamagawa measure and the adelic Poisson summation formula rest.
--
--   **Formalization Note** The functoriality in finite extensions $F'/F$ mentioned in the source is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.1.2.1, Lemma A.1.2.1, eqs. (A.1.2.1)–(A.1.2.2), pp. 540–541

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem adele_class_group_compact (F : Type*) [Field F] [NumberField F] :
    (∀ A : Set F, IsClosed (algebraMap F (AdeleRing (𝓞 F) F) '' A)) ∧
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) ∧
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
    T2Space (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
    (∀ n : ℕ, 0 < n → Function.Bijective
      (fun x : AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F => n • x)) ∧
    (∀ x : AdeleRing (𝓞 F) F, ∃ y : AdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), y.2 v ∈ v.adicCompletionIntegers F) ∧
      ∃ ξ : F, x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∧
    (∀ ξ : F, (∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 v ∈ v.adicCompletionIntegers F) ↔
      ξ ∈ (algebraMap (𝓞 F) F).range) ∧
    (∀ U : Set (AdeleRing (𝓞 F) F), IsOpen U → IsOpen
      ((QuotientAddGroup.mk :
          AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ''
        (U ∩ {y | ∀ v : HeightOneSpectrum (𝓞 F), y.2 v ∈ v.adicCompletionIntegers F}))) := by sorry

end MasulloGRH
