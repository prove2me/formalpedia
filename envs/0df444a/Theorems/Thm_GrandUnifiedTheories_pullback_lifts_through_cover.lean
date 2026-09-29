-- Prove2me | Theorems.Thm_GrandUnifiedTheories_pullback_lifts_through_cover
-- name    : GrandUnifiedTheories.pullback_lifts_through_cover
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:04:21.263901+00:00
-- url     : https://prove2.me/theorems/46b44f52-ed70-4425-96bd-b2da647ad4c2
-- title:
--   Theorem 9: lifting the pullback square through the double cover
-- statement:
--   Theorem 9 of the source upgrades Theorem 8 from $\mathrm{SO}(10)$ to its double cover:
--
--   $$G_{\mathrm{SM}}/\mathbb{Z}_6 \;=\; \mathrm{SU}(5)\cap\bigl(\mathrm{Spin}(4)\times\mathrm{Spin}(6)\bigr)/\mathbb{Z}_2 \;\subseteq\; \mathrm{Spin}(10),$$
--
--   and its proof is "a little diagram chase". This milestone is exactly that diagram chase, stated for arbitrary groups so that no construction of $\mathrm{Spin}(10)$ is required.
--
--   Given group homomorphisms
--
--   $$\tilde\varphi : G_1\to G_2,\quad \tilde\theta : G_1\to H_1,\quad \psi : G_2\to H_2,\quad \tilde\eta : H_1\to H_2,\quad q : H_1\to K_1,\quad p : H_2\to K_2,\quad i : K_1\to K_2$$
--
--   such that both squares commute, i.e. $\tilde\eta\circ\tilde\theta = \psi\circ\tilde\varphi$ and $i\circ q = p\circ\tilde\eta$, such that $\tilde\eta$ is injective, and such that the outer square is a pullback in the sense that every pair $(g', k)\in G_2\times K_1$ with $i(k) = p(\psi(g'))$ comes from some $x\in G_1$ with $q(\tilde\theta(x)) = k$ and $\tilde\varphi(x) = g'$: then the upper square is a pullback as well. That is, whenever $g\in H_1$ and $g'\in G_2$ satisfy $\tilde\eta(g) = \psi(g')$, there is an $x\in G_1$ with $\tilde\theta(x) = g$ and $\tilde\varphi(x) = g'$.
--
--   Taking $G_1 = G_{\mathrm{SM}}/\mathbb{Z}_6$, $G_2 = \mathrm{SU}(5)$, $H_1 = (\mathrm{Spin}(4)\times\mathrm{Spin}(6))/\mathbb{Z}_2$, $H_2 = \mathrm{Spin}(10)$, $K_1 = \mathrm{SO}(4)\times\mathrm{SO}(6)$ and $K_2 = \mathrm{SO}(10)$, with $p$ and $q$ the two-to-one covering maps, the outer square is the content of Theorem 8 and the conclusion is Theorem 9.
--
--   **Formalization note.** The hypotheses are exactly the properties of the published diagram that its proof uses; they are satisfiable, being satisfied by the $\mathrm{Spin}$ data of the source. Constructing $\mathrm{Spin}(10)$, its covering homomorphism onto $\mathrm{SO}(10)$, and the lift $\psi$ of the inclusion $\mathrm{SU}(5)\hookrightarrow\mathrm{SO}(10)$ is outside the scope of this milestone.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 4, p. 69, Theorem 9 and its proof ('From this, a little diagram chase proves our earlier claim')

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem pullback_lifts_through_cover
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    [Group K₁] [Group K₂]
    (phiTilde : G₁ →* G₂) (thetaTilde : G₁ →* H₁) (psi : G₂ →* H₂) (etaTilde : H₁ →* H₂)
    (q : H₁ →* K₁) (p : H₂ →* K₂) (i : K₁ →* K₂)
    (hUpper : ∀ x : G₁, etaTilde (thetaTilde x) = psi (phiTilde x))
    (hLower : ∀ g : H₁, i (q g) = p (etaTilde g))
    (hEta : Function.Injective etaTilde)
    (hOuter : ∀ (g' : G₂) (k : K₁), i k = p (psi g') →
      ∃ x : G₁, q (thetaTilde x) = k ∧ phiTilde x = g') :
    ∀ (g : H₁) (g' : G₂), etaTilde g = psi g' →
      ∃ x : G₁, thetaTilde x = g ∧ phiTilde x = g' := by sorry

end GrandUnifiedTheories
