-- Prove2me | Theorems.Thm_GroupoidSchreier_Interpretation_proposition_2_4
-- name    : GroupoidSchreier.Interpretation.proposition_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:42.603046+00:00
-- url     : https://prove2.me/theorems/c44e4540-48cf-4d44-bca5-11a82b0e8f3c
-- title:
--   Proposition 2.4, p. 6 — for a weak action, σ₁₁ = 1 forces σ_{u1} = σ_{1u} = 1
-- statement:
--   Let $\langle F,\sigma\rangle$ be a weak action of a groupoid $\mathcal G$ on a family of groups $\mathcal K$ (Proposition 2.6). Its axiom $\sigma_{11} = 1$ is the weak coherence with the identity law (LF3′). Proposition 2.4 says that, because 2-cells of the codomain $\mathrm{AUT}(\mathcal K)$ are invertible, LF3′ implies the full coherence with the identity law (LF3): for every arrow $u : A\to B$,
--
--   $$\sigma_{u1_A} = 1 = \sigma_{1_B u}.$$
--
--   This is what makes $(1,1)$ a two-sided identity of the twisted product groupoid.
--
--   **Formalization Note** The paper states Proposition 2.4 for lax 2-functors into any 2-category whose 2-cells are invertible; it is posed here for the codomain $\mathrm{AUT}(\mathcal K)$, where the axioms 1, 2, 4 of a weak action are LF1, LF3′, LF2 and the identity 2-cell on $F(u)$ is the element $1\in K_B$. $\sigma_{u1_A}$ (the pair $1_A$ then $u$) is `F.σ (𝟙 A) u`; $\sigma_{1_B u}$ is `F.σ u (𝟙 B)`.
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, p. 6, Proposition 2.4 (with LF3 of Definition 2.3, p. 6)

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem proposition_2_4 {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) {A B : G} (u : A ⟶ B) :
    F.σ (𝟙 A) u = 1 ∧ F.σ u (𝟙 B) = 1 := by sorry
end GroupoidSchreier.Interpretation
