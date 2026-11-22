-- Prove2me | Theorems.Thm_MasulloGRH_expWeighted_projective_isFrechet
-- name    : MasulloGRH.expWeighted_projective_isFrechet
-- status  : Proved
-- author  : @kirisame
-- created : 2026-11-21T18:58:06.248024+00:00
-- url     : https://prove2.me/theorems/878cd65a-7067-43c7-b4c3-b1a9ce013562
-- title:
--   Lemma D.3.3.2 / Example D.3.3.5 — exponentially weighted Schwartz functions on an elementary group form a Fréchet space
-- statement:
--   Let $E=\mathbb R^{m}\times\mathbb T^{n}\times\mathbb Z^{r}\times F$ be an elementary abelian Lie group ($F$ a finite abelian group), let $\mu\colon E\to\mathbb R_{>0}$ be a continuous homomorphism, and let $I\subset\mathbb R$ be a non-empty interval. Consider the space
--   $$\mathcal S_I(E,\mu)=\{\phi\colon E\to\mathbb C\ :\ \mu^{a}\phi\in\mathcal S(E)\ \text{for all } a\in I\}$$
--   with the projective topology of the operators $T_a\phi=\mu^{a}\phi$ into the Schwartz space $\mathcal S(E)$, $a\in I$. Then $\mathcal S_I(E,\mu)$ is a Fréchet space: it is locally convex, complete and metrizable.
--
--   The space is given abstractly. Let $X$ be a complex vector space with a topology and linear maps $W_a\colon X\to\mathcal S(E)$, $a\in\mathbb R$, such that
--
--   - $W_ax=\mu^{a-b}\,W_bx$ pointwise on $E$ for all $a,b\in I$ and $x\in X$;
--   - the topology of $X$ is the projective topology of the maps $W_a$, $a\in I$;
--   - $x=0$ whenever $W_ax=0$ for all $a\in I$;
--   - every family $(g_a)_{a\in I}$ in $\mathcal S(E)$ with $g_a=\mu^{a-b}g_b$ for all $a,b\in I$ is of the form $g_a=W_ax$ for some $x\in X$.
--
--   Then $X$ is a Fréchet space.
--
--   Metrizability rests on the interpolation estimate behind Lemma D.3.3.2: for $a<c<b$ the Schwartz seminorms of $\mu^{c}\phi$ are bounded by those of $\mu^{a}\phi$ and $\mu^{b}\phi$, so countably many exponents define the topology. Completeness holds because a pointwise limit of compatible families is compatible.
--
--   **Formalization Note** The finite group is $F=\prod_i\mathbb Z/d_i$ with all $d_i\ne0$. The homomorphism property of $\mu$ is stated as $\mu(e+e')=\mu(e)\mu(e')$ together with positivity. Nuclearity of these spaces is not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3, Lemma D.3.3.2 and Example D.3.3.5, pp. 804–805 (Fréchet property of $\mathcal S_I(k,G)$ for $G/k$ an elementary abelian Lie group)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expWeighted_projective_isFrechet
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e)
    (hμmul : ∀ e e', μ (e + e') = μ e * μ e') (hμc : Continuous μ)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty)
    (X : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (W : ℝ → X →ₗ[ℂ] ElemSchwartz m n r s d)
    (hW : ∀ a ∈ I, ∀ b ∈ I, ∀ (x : X) (e : ElemGroup m n r s d),
      (W a x).toFun e = ((μ e ^ (a - b) : ℝ) : ℂ) * (W b x).toFun e)
    (htop : ‹TopologicalSpace X› =
      ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (W a) inferInstance)
    (hinj : ∀ x : X, (∀ a ∈ I, W a x = 0) → x = 0)
    (hsurj : ∀ g : ℝ → ElemSchwartz m n r s d,
      (∀ a ∈ I, ∀ b ∈ I, ∀ e : ElemGroup m n r s d,
        (g a).toFun e = ((μ e ^ (a - b) : ℝ) : ℂ) * (g b).toFun e) →
      ∃ x : X, ∀ a ∈ I, W a x = g a) :
    IsFrechet X := by
  sorry

end MasulloGRH
