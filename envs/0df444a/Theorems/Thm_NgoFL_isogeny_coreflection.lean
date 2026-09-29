-- Prove2me | Theorems.Thm_NgoFL_isogeny_coreflection
-- name    : NgoFL.isogeny_coreflection
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T22:51:55.287998+00:00
-- url     : https://prove2.me/theorems/1871e631-e241-49b0-9ccb-ca3425b60f60
-- title:
--   A matched pair of root lines gives a matched pair of reflections
-- statement:
--   Let $(\psi^*, \psi_*)$ be an isogeny of root data between two pinned split reductive groups
--   $G_1$ and $G_2$, in the sense of Ngo's Definition 1.12.1. Suppose a root $\beta$ of $\Phi_2$ and
--   a root $\alpha$ of $\Phi_1$ are matched, in the sense that
--
--   $$ \psi^*(\beta) = c\,\alpha \quad\text{and}\quad \psi_*(\alpha^\vee) = c\,\beta^\vee $$
--
--   for one and the same rational scalar $c$. Then $\psi_*$ intertwines the two reflections of the
--   Cartan subalgebras:
--
--   $$ \psi_*\bigl(s_\alpha(x)\bigr) \;=\; s_\beta\bigl(\psi_*(x)\bigr)
--      \qquad \text{for all } x \in X_*(T_1)\otimes\mathbb{Q}, $$
--
--   where $s_\alpha(x) = x - \langle \alpha, x\rangle\,\alpha^\vee$ and
--   $s_\beta(y) = y - \langle\beta, y\rangle\,\beta^\vee$.
--
--   This is the computation underlying Ngo's remark 1.12.4 that, since the reflection attached to a
--   root depends only on the line through the root, an isogeny of root data induces an isomorphism
--   $W_1 \simeq W_2$ of Weyl groups. It isolates the step where the transposition property is used:
--   $\langle\beta, \psi_* x\rangle = \langle \psi^*\beta, x\rangle = c\,\langle\alpha,x\rangle$.
--   That the two scalars agree is not an extra assumption in Ngo's setting but a consequence of
--   transposition and $\langle\alpha,\alpha^\vee\rangle = 2$; here it is taken as a hypothesis so
--   that this milestone isolates the reflection computation alone.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 24, 1.12.4 (the isogeny induces an isomorphism of Weyl groups)

import Mathlib
import Definitions.Def_NgoRootDatumIsogeny

namespace NgoFL

theorem isogeny_coreflection {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    (b₁ : Set ι₁) (b₂ : Set ι₂) (psiStar : M₂ ≃ₗ[ℚ] M₁) (psiLower : N₁ ≃ₗ[ℚ] N₂)
    (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower)
    (i₁ : ι₁) (i₂ : ι₂) (c : ℚ)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁)
    (hcoroot : psiLower (P₁.coroot i₁) = c • P₂.coroot i₂) (x : N₁) :
    psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by sorry

end NgoFL
