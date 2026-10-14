-- Prove2me | Theorems.Thm_MoritaEquiv_nonempty_equivalence_discrete_of_classifier
-- name    : MoritaEquiv.nonempty_equivalence_discrete_of_classifier
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-13T19:12:54.70196+00:00
-- url     : https://prove2.me/theorems/cee02edb-9538-4c48-880f-ff53d96b84e6
-- title:
--   A thin category classified by a surjective invariant is equivalent to a discrete category
-- statement:
--   Let $\mathcal C$ be a category in which every hom-set has at most one element, and let $\varphi:\mathrm{Ob}(\mathcal C)\to\alpha$ be a surjective map to a set $\alpha$ such that, for all objects $X, Y$, there is a morphism $X\to Y$ if and only if $\varphi(X)=\varphi(Y)$.
--
--   **Statement.** Then $\mathcal C$ is equivalent to the discrete category on $\alpha$.
--
--   The functor $X\mapsto\varphi(X)$ is faithful because hom-sets are subsingletons, full by the hypothesis on morphisms, and essentially surjective because $\varphi$ is surjective. The lemma covers categories of models that are "discrete up to isomorphism", for example the categories of models of the theories in Barrett–Halvorson's Theorem 5.2. There $\varphi$ sends a model to its isomorphism invariant, and two such categories are equivalent as soon as the sets of invariants are in bijection.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675, §5 (proof of Theorem 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- A category whose hom-sets are subsingletons, together with a surjective "classifying" map
`φ : C → α` such that there is a morphism `X ⟶ Y` exactly when `φ X = φ Y`, is equivalent to the
discrete category on `α`. -/
theorem nonempty_equivalence_discrete_of_classifier {C : Type*} [Category C] {α : Type*}
    (φ : C → α) (hsurj : Function.Surjective φ) (hsub : ∀ X Y : C, Subsingleton (X ⟶ Y))
    (hhom : ∀ X Y : C, Nonempty (X ⟶ Y) ↔ φ X = φ Y) : Nonempty (C ≌ Discrete α) := by sorry

end MoritaEquiv
