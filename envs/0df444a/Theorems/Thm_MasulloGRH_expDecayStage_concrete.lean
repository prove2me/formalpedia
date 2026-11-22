-- Prove2me | Theorems.Thm_MasulloGRH_expDecayStage_concrete
-- name    : MasulloGRH.expDecayStage_concrete
-- status  : Proved
-- author  : @kirisame
-- created : 2026-11-21T18:58:19.414182+00:00
-- url     : https://prove2.me/theorems/6d7fb168-ec83-4f23-a21d-578dbc86b441
-- title:
--   Concrete description of the stage $\mathcal S_I(k,G)$ on the elementary quotient $G/k$
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, let $I\subset\mathbb R$ be a non-empty set of exponents and let $k\subset G$ be a good subgroup (a compact subgroup whose annihilator $k^\perp\subset\widehat G$ is open and compactly generated). Let $\mathcal S_I(k,G)$ be the stage of $k$-invariant elements of $\mathcal S_I(G)$, with the projective topology of the operators $T_a\colon\mathcal S_I(k,G)\to\mathcal S(G/k)$, $T_a\phi=|\cdot|_G^a\phi$, $a\in I$ (Definition D.3.3.3).
--
--   1. The pair $(G,k)$ is structural: $G$ is compactly generated, so $G/k$ is an elementary abelian Lie group.
--   2. The stage $\mathcal S_I(k,G)$ is a nuclear space.
--   3. Let $\pi\colon G\to E=\mathbb R^{m}\times\mathbb T^{n}\times\mathbb Z^{r}\times F$ be any presentation of $G/k$ as an elementary group (a continuous open surjective homomorphism with kernel $k$). Then there are linear maps $W_a\colon\mathcal S_I(k,G)\to\mathcal S(E)$, $a\in\mathbb R$, with the following properties.
--      - For $a\in I$, $W_a\phi$ is the function $|\cdot|_G^a\phi$ viewed on $E$:
--      $$(W_a\phi)(\pi(x))=|x|_G^{a}\,\phi(x)\qquad(x\in G).$$
--      - The topology of $\mathcal S_I(k,G)$ is the projective topology of the maps $W_a$, $a\in I$.
--      - Every compatible family is attained: if $g_a\in\mathcal S(E)$, $a\in I$, satisfy
--      $$g_a(\pi(x))=|x|_G^{a-b}\,g_b(\pi(x))\qquad(a,b\in I,\ x\in G),$$
--      then there is $\phi\in\mathcal S_I(k,G)$ with $W_a\phi=g_a$ for all $a\in I$.
--
--   This replaces the Schwartz–Bruhat space of the abstract quotient $G/k$ by the concrete space $\mathcal S(E)$ of smooth rapidly decreasing functions on the elementary group, which is the form in which the source treats $\mathcal S_I(k,G)$.
--
--   **Formalization Note** The presentation is a homomorphism defined on the subgroup $\top$ of $G$ with values in the multiplicative copy of $E$, as in the definition of a structural pair. The maps $W_a$ are given for every real $a$ and are only constrained for $a\in I$. The interval hypothesis on $I$ is not needed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3, Definition D.3.3.3 and Example D.3.3.5, pp. 805–806 (the identification $\mathcal S(k,G)=\mathcal S(G/k)$ and the passage to $G/k=\mathbb R_{>0}\times(G^1/k)$ used in the proofs of Lemma D.3.3.2 and Theorem D.3.3.7)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecayStage_concrete
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsStructuralPair ⊤ k ∧ IsNuclear (ExpDecayStage G m I k) ∧
    ∀ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : ↥(⊤ : Subgroup G) →* Multiplicative (ElemGroup m' n' r' s' d')),
      IsElemPresentation ⊤ k π →
      ∃ W : ℝ → ExpDecayStage G m I k →ₗ[ℂ] ElemSchwartz m' n' r' s' d',
        (∀ a ∈ I, ∀ (ϕ : ExpDecayStage G m I k) (x : G),
          (W a ϕ).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
            ((m x ^ a : ℝ) : ℂ) * (ExpDecayStage.incl G m I k ϕ).toFun x) ∧
        (inferInstance : TopologicalSpace (ExpDecayStage G m I k)) =
          ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (W a) inferInstance ∧
        ∀ g : ℝ → ElemSchwartz m' n' r' s' d',
          (∀ a ∈ I, ∀ b ∈ I, ∀ x : G,
            (g a).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) =
              ((m x ^ (a - b) : ℝ) : ℂ) *
                (g b).toFun (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩))) →
          ∃ ϕ : ExpDecayStage G m I k, ∀ a ∈ I, W a ϕ = g a := by
  sorry

end MasulloGRH
