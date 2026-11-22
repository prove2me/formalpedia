-- Prove2me | Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
-- name    : MasulloGRH.exists_elemPresentation_of_isStructuralPair
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T14:38:30.689437+00:00
-- url     : https://prove2.me/theorems/a5834a72-c01c-4c43-9617-2380a6cbe369
-- title:
--   For a structural pair $(\Gamma,k)$, $\Gamma/k$ is an elementary abelian Lie group
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group and let $(\Gamma,k)$ be a **structural pair** of $G$: $\Gamma$ is an open, compactly generated subgroup of $G$, $k$ is a good subgroup of $G$ (closed, with annihilator $k^\perp\subseteq\widehat G$ open and compactly generated), and $k\subseteq\Gamma$. Then $\Gamma/k$ is an elementary abelian Lie group. In other words, there are integers $m,n,r,s\ge0$, positive integers $d_1,\dots,d_s$, and a continuous, open, surjective homomorphism
--
--   $$
--   \pi\colon\ \Gamma\longrightarrow \mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\prod_{i=1}^{s}\mathbb Z/d_i\mathbb Z,\qquad \mathbb T=\mathbb R/\mathbb Z,
--   $$
--
--   whose kernel is exactly $k$. Equivalently, $\pi$ induces an isomorphism of topological groups $\phi_0\colon\Gamma/k\xrightarrow{\ \sim\ }\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$, as in (D.1.5.3).
--
--   This is Lemma D.1.5.2(1). It guarantees that every structural pair has a presentation, so the space $\mathcal S(k,\Gamma)=\mathcal S(\Gamma/k)$ of Schwartz–Bruhat functions supported on $\Gamma$ and invariant under $k$ is defined for every structural pair.
--
--   **Formalization Note** The finite abelian group $F$ is written as $\prod_{i<s}\mathbb Z/d_i\mathbb Z$, and the condition $d_i\ne0$ is part of `IsElemPresentation`. The homomorphism is valued in the multiplicative version of the additive group `ElemGroup m n r s d`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.5.2(1) and its proof (p. 761), with Definition D.1.5.1 (p. 760) and (D.1.5.3) (p. 762)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem exists_elemPresentation_of_isStructuralPair
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ k : Subgroup G) (h : IsStructuralPair Γ k) :
    ∃ (m n r s : ℕ) (d : Fin s → ℕ) (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)),
      IsElemPresentation Γ k π := by
  sorry

end MasulloGRH
