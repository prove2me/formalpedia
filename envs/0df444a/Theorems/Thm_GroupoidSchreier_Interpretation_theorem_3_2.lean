-- Prove2me | Theorems.Thm_GroupoidSchreier_Interpretation_theorem_3_2
-- name    : GroupoidSchreier.Interpretation.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:36.882771+00:00
-- url     : https://prove2.me/theorems/7dcee340-ae0c-41a3-a022-061babed1481
-- title:
--   Theorem 3.2, p. 15 — the twisted product ∫_G : Act~(G, K) → Ext(G, K) is an equivalence of categories
-- statement:
--   Let $\mathcal G$ be a groupoid and $\mathcal K$ a family of groups indexed by its objects. Theorem 3.2 states that the twisted product is an equivalence of categories
--
--   $$\int_{\mathcal G} : \widetilde{\mathrm{Act}}(\mathcal G,\mathcal K)\longrightarrow \mathrm{Ext}(\mathcal G,\mathcal K).$$
--
--   It is stated here through the fiber relation (Example 2.15), which inverts $\int_{\mathcal G}$ up to isomorphism:
--
--   1. every weak action is a fiber weak action of some extension;
--   2. every extension has a fiber weak action;
--   3. (full faithfulness) whenever $F_1$ is the fiber of $\mathcal E_1$ along a normalized section $f\mapsto\tilde f^{\,1}$ and $F_2$ the fiber of $\mathcal E_2$ along $f\mapsto \tilde f^{\,2}$, there is a bijection $\Gamma\mapsto\tau^\Gamma$ between morphisms of extensions $\Gamma : \mathcal E_1\to\mathcal E_2$ and morphisms of weak actions $\tau : F_1\to F_2$, determined by
--
--   $$\Gamma\big(\tilde u^{\,1}\big) = \tau^\Gamma(u)^{-1}\,\tilde u^{\,2}\qquad\text{for every arrow } u \text{ of } \mathcal G.$$
--
--   **Formalization Note** "Equivalence of categories" is posed as essential surjectivity in both directions through the fiber relation together with a hom bijection given by an explicit formula; the categories are not built as Mathlib categories. In the formula $\tau^\Gamma(u)^{-1}\in K_B$ is read in $\mathcal E_2$ through the fiber identification $\iota$, and the product is composition in $\mathcal E_2$ (functional order).
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, p. 15, Theorem 3.2

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem theorem_3_2 {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] :
    (∀ F : WeakAction G K, ∃ E : Extension G K, IsFiberAction E F) ∧
    (∀ E : Extension G K, ∃ F : WeakAction G K, IsFiberAction E F) ∧
    ∀ (E₁ E₂ : Extension G K)
      (s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B) (s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B)
      (F₁ F₂ : WeakAction G K),
      IsNormalizedSection E₁ s₁ → FiberVia E₁ s₁ F₁ →
      IsNormalizedSection E₂ s₂ → FiberVia E₂ s₂ F₂ →
      ∃ e : ExtHom E₁ E₂ ≃ ActHom F₁ F₂,
        ∀ (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B),
          Γ.map (s₁ u) = E₂.comp (E₂.ι B ((e Γ).τ u)⁻¹) (s₂ u) := by sorry
end GroupoidSchreier.Interpretation
