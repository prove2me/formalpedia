-- Prove2me | Theorems.Thm_NgoFL_isogeny_weyl_equivariant
-- name    : NgoFL.isogeny_weyl_equivariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:30:08.577442+00:00
-- url     : https://prove2.me/theorems/13be68b5-a571-4620-8c30-c221e3aa685f
-- title:
--   1.12.4 / 1.12.6: $\psi_*$ conjugates $W_1$ onto $W_2$
-- statement:
--   Let $(\psi^*, \psi_*)$ be an isogeny of root data between two pinned split reductive groups
--   $G_1$ and $G_2$, in the sense of Ngo's Definition 1.12.1, and let $W_1$ and $W_2$ be the Weyl
--   groups of $\Phi_1$ and $\Phi_2$ acting on the Cartan subalgebras
--   $\mathfrak{t}_i = X_*(T_i)\otimes\mathbb{Q}$.
--
--   The statement is that $\psi_* : \mathfrak{t}_1 \to \mathfrak{t}_2$ intertwines the two Weyl
--   group actions in both directions: for every $w \in W_1$ there is $w' \in W_2$ with
--   $\psi_*(wx) = w'(\psi_* x)$ for all $x$, and for every $w' \in W_2$ there is $w \in W_1$ with
--   the same identity. Equivalently, conjugation by $\psi_*$ carries $W_1$ isomorphically onto
--   $W_2$.
--
--   This is Ngo's observation 1.12.4 — since the reflection attached to a root depends only on the
--   $\mathbb{Q}$-line through that root, the bijection of root lines induced by $\psi^*$ transports
--   reflections to reflections — and it is the step that makes Lemme 1.12.6 work: a $W$-equivariant
--   isomorphism $\mathfrak{t}_1 \to \mathfrak{t}_2$ descends to an isomorphism
--
--   $$ \nu : \mathfrak{c}_{G_1} = \mathfrak{t}_1/\!/W_1 \;\longrightarrow\;
--      \mathfrak{t}_2/\!/W_2 = \mathfrak{c}_{G_2} $$
--
--   of the spaces of characteristic polynomials, which is what lets the two stable classes $a_1$ and
--   $a_2$ of the non-standard fundamental lemma (Theoreme 1.12.7) be said to correspond.
--
--   The substance is that the bijection $\Phi_2 \to \Phi_1$ on root lines induced by $\psi^*$ and
--   the bijection $\Phi_1^\vee \to \Phi_2^\vee$ on coroot lines induced by $\psi_*$ are the same
--   bijection, with the same proportionality constants; only then does a reflection go to a
--   reflection.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 24, 1.12.4 and Lemme 1.12.6 (canonical isomorphisms $\mathfrak{t}_1 \to \mathfrak{t}_2$ and $\nu : \mathfrak{c}_{G_1} \to \mathfrak{c}_{G_2}$)

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant
import Definitions.Def_NgoRootDatumIsogeny

namespace NgoFL

theorem isogeny_weyl_equivariant {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] [Fintype ι₁] [Fintype ι₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁)
    (P₂ : RootPairing ι₂ ℚ M₂ N₂) [P₁.IsRootSystem] [P₂.IsRootSystem] [P₁.IsReduced]
    [P₂.IsReduced] (b₁ : Set ι₁) (b₂ : Set ι₂) (psiStar : M₂ ≃ₗ[ℚ] M₁)
    (psiLower : N₁ ≃ₗ[ℚ] N₂) (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower) :
    (∀ w ∈ weylSubgroup P₁ Set.univ, ∃ w' ∈ weylSubgroup P₂ Set.univ,
        ∀ x : N₁, psiLower (w x) = w' (psiLower x)) ∧
      (∀ w' ∈ weylSubgroup P₂ Set.univ, ∃ w ∈ weylSubgroup P₁ Set.univ,
        ∀ x : N₁, psiLower (w x) = w' (psiLower x)) := by sorry

end NgoFL
