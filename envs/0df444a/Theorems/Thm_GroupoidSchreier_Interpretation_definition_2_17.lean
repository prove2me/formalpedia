-- Prove2me | Theorems.Thm_GroupoidSchreier_Interpretation_definition_2_17
-- name    : GroupoidSchreier.Interpretation.definition_2_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:32.959665+00:00
-- url     : https://prove2.me/theorems/0402f06d-eaf1-483c-be24-6c5a44879f1f
-- title:
--   Definition 2.17, pp. 12–13 — the twisted product of a weak action is an extension whose fiber weak action is F
-- statement:
--   Let $\langle F,\sigma\rangle$ be a weak action of a groupoid $\mathcal G$ on a family of groups $\mathcal K$. The twisted product $\int_{\mathcal G}F$ has the objects of $\mathcal G$; its arrows $A\to B$ are the pairs $(f,\lambda)$ with $f : A\to B$ in $\mathcal G$ and $\lambda\in K_B$; composition and identities are
--
--   $$(g,\mu)(f,\lambda) = \big(gf,\ \mu\,{}^g\lambda\,\sigma_{gf}\big),\qquad 1_A = (1_A, 1).$$
--
--   Definition 2.17 asserts that this is a groupoid and that the projection $(f,\lambda)\mapsto f$ is a fibration with fiber over $A$ the group $K_A$ (identified with the arrows $(1_A,k)$). The statement here says: there is an extension $\mathcal E$ of $\mathcal G$ by $\mathcal K$ together with bijections $\varphi_{AB} : \mathcal E(A,B)\cong\mathcal G(A,B)\times K_B$ that carry composition to the twisted composition above, identities to $(1_A,1)$, the projection $P$ to the first component, and the fiber element $k\in K_A$ to $(1_A,k)$; moreover $F$ is the fiber weak action of $\mathcal E$ along the section $f\mapsto\varphi^{-1}(f,1)$.
--
--   This is the passage from 2-cocycles to extensions in the classification of groupoid extensions.
--
--   **Formalization Note** The paper's Definition 2.17 is stated for lax 2-functors into groupoids; it is posed here for weak actions (every $F(X) = K_X$ a one-object groupoid), the case used in Theorem 3.2 (compare Example 2.19, p. 14). The last clause (the section $f\mapsto(f,1)$ recovers $F$) is the identification of the fiber of $\int_{\mathcal G}F$ with $F$ stated on p. 13.
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, pp. 12–13, Definition 2.17

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem definition_2_17 {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) :
    ∃ (E : Extension G K) (φ : ∀ A B : G, E.Hom A B ≃ (A ⟶ B) × K B),
      (∀ (A B C : G) (g : E.Hom B C) (f : E.Hom A B),
        φ A C (E.comp g f) = twistedComp F (φ B C g) (φ A B f)) ∧
      (∀ A : G, φ A A (E.id A) = (𝟙 A, 1)) ∧
      (∀ (A B : G) (e : E.Hom A B), E.P e = (φ A B e).1) ∧
      (∀ (A : G) (k : K A), φ A A (E.ι A k) = (𝟙 A, k)) ∧
      FiberVia E (fun ⦃A B : G⦄ (u : A ⟶ B) => (φ A B).symm (u, 1)) F := by sorry
end GroupoidSchreier.Interpretation
