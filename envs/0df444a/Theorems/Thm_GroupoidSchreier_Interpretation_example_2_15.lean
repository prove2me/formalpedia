-- Prove2me | Theorems.Thm_GroupoidSchreier_Interpretation_example_2_15
-- name    : GroupoidSchreier.Interpretation.example_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:28.294454+00:00
-- url     : https://prove2.me/theorems/1e260641-b6eb-4f60-b974-7ed424b00d01
-- title:
--   Example 2.15, pp. 11–12 — a normalized section of an extension determines a weak action (the fiber)
-- statement:
--   Let $P : \mathcal E\to\mathcal G$ be an extension of a groupoid $\mathcal G$ by a family of groups $\mathcal K$ (a fibration bijective on objects with fibers $K_A$). Then:
--
--   1. a normalized section exists: one may choose, for each arrow $f$ of $\mathcal G$, an arrow $\tilde f$ of $\mathcal E$ with $P(\tilde f) = f$ and $\tilde 1 = 1$;
--   2. every such section determines a weak action $\langle F,\sigma\rangle$ of $\mathcal G$ on $\mathcal K$, the fiber of $\mathcal E$, given by
--
--   $$ {}^f k = \tilde f\, k\,\tilde f^{-1},\qquad \sigma_{gf} = \tilde g\,\tilde f\,\big(\widetilde{gf}\big)^{-1}.$$
--
--   This is the passage from extensions to 2-cocycles in the classification of groupoid extensions (p. 12: "any lax 2-functor fiber $F^*$ determines a weak action of the base groupoid on the family of groups determined by the fibers").
--
--   **Formalization Note** Part 2 asserts that there is a weak action (a structure satisfying conditions 1–4 of Proposition 2.6 with each ${}^f(-)$ a group isomorphism) whose $F$ and $\sigma$ satisfy the two displayed equations, read in $\mathcal E$ through the fiber identification $\iota$.
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, pp. 11–12, Example 2.15 and the claim following it on p. 12

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem example_2_15 {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) :
    (∃ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s) ∧
      ∀ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s →
        ∃ F : WeakAction G K, FiberVia E s F := by sorry
end GroupoidSchreier.Interpretation
