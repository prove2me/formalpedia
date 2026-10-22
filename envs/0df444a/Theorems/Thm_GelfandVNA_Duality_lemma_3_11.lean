-- Prove2me | Theorems.Thm_GelfandVNA_Duality_lemma_3_11
-- name    : GelfandVNA.Duality.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:55.044515+00:00
-- url     : https://prove2.me/theorems/7e945312-cd86-4aa0-91f6-42e1239912a8
-- title:
--   Lemma 3.11 (Def 3.10), pp. 24–25 — ProjAlg is a functor CVNA → LBAlg
-- statement:
--   Let $f\colon A\to B$ be a normal unital \*-homomorphism of commutative von Neumann algebras. Then:
--
--   1. $\mathsf{ProjAlg}(A)$ is a localizable Boolean algebra: it is order-isomorphic to a complete Boolean algebra in which $1$ is the supremum of the elements $a$ whose principal algebra admits a finite faithful continuous valuation;
--   2. the restriction $\mathsf{ProjAlg}(f)\colon\mathsf{ProjAlg}(A)\to\mathsf{ProjAlg}(B)$ is a homomorphism of Boolean algebras (it preserves $\wedge$, $\vee$, complements, $0$ and $1$);
--   3. $\mathsf{ProjAlg}(f)$ preserves all existing suprema:
--   $$s=\sup S\ \Longrightarrow\ \mathsf{ProjAlg}(f)(s)=\sup\,\mathsf{ProjAlg}(f)(S).$$
--
--   This is the content of "Definition 3.10 is correct": $\mathsf{ProjLoc}=\mathsf{ProjAlg}^{\mathrm{op}}\colon\mathsf{CVNA}^{\mathrm{op}}\to\mathsf{MLoc}$ is a functor.
--
--   **Formalization Note** Because the Boolean algebra structure of `ProjAlg A` is not bundled as a complete one, localizability is stated through an order isomorphism onto a complete Boolean algebra satisfying `HasFiniteValuationCover`.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, pp. 24–25, Definition 3.10, Lemma 3.11

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_VNA

namespace GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Lemma 3.11 with Definition 3.10, pp. 24–25: `ProjAlg` is a functor `CVNA → LBAlg`. The algebra
`ProjAlg(A)` is (order-isomorphic to) a localizable Boolean algebra, and for a normal
*-homomorphism `f : A → B` the restriction `ProjAlg(f)` is a homomorphism of Boolean algebras that
preserves all existing suprema. -/
theorem lemma_3_11 (A B : Type u) [CommCStarAlgebra A] [WStarAlgebra A]
    [CommCStarAlgebra B] [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f) :
    (∃ (C : Type u) (_ : CompleteBooleanAlgebra C),
      HasFiniteValuationCover C ∧ Nonempty (ProjAlg A ≃o C)) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊓ q) = projMap f p ⊓ projMap f q) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊔ q) = projMap f p ⊔ projMap f q) ∧
    (∀ p : ProjAlg A, projMap f pᶜ = (projMap f p)ᶜ) ∧
    projMap f ⊥ = ⊥ ∧ projMap f ⊤ = ⊤ ∧
    (∀ (s : Set (ProjAlg A)) (a : ProjAlg A), IsLUB s a →
      IsLUB (projMap f '' s) (projMap f a)) := by sorry

end GelfandVNA.Duality
