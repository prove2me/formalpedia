-- Prove2me | Theorems.Thm_MasulloGRH_exists_cofinal_structuralPairs
-- name    : MasulloGRH.exists_cofinal_structuralPairs
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T13:44:00.045187+00:00
-- url     : https://prove2.me/theorems/1d7860c4-b55d-4090-95df-2e0c393e6a5d
-- title:
--   A cofinal sequence of structural pairs
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group. Recall that a pair $(\Gamma,k)$ of subgroups of $G$ is *structural* if $\Gamma$ is open and compactly generated, $k\subseteq\Gamma$ is a good subgroup (closed, with open and compactly generated annihilator $k^\perp\subseteq\widehat G$), and a *presentation* of $\Gamma/k$ is an isomorphism of topological groups $\Gamma/k\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with $F$ finite abelian.
--
--   Then there is a sequence of structural pairs $(\Gamma_N,k_N)_{N\in\mathbb N}$, each with a presentation of $\Gamma_N/k_N$, such that
--   $$\Gamma_0\subseteq\Gamma_1\subseteq\Gamma_2\subseteq\cdots,\qquad k_0\supseteq k_1\supseteq k_2\supseteq\cdots,$$
--   and which is **cofinal**: for every structural pair $(\Gamma,k)$ admitting a presentation of $\Gamma/k$ there is an $M$ with
--   $$\Gamma\subseteq\Gamma_M\quad\text{and}\quad k_M\subseteq k.$$
--
--   This is the countability statement behind Bruhat's description of $\mathcal S(G)$ as a countable inductive limit: the directed system of structural pairs, ordered by $(\Gamma,k)\le(\Gamma',k')$ iff $\Gamma\subseteq\Gamma'$ and $k'\subseteq k$, has a cofinal sequence.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5, proof of Theorem D.1.5.7, pp. 760–764 (and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961))

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem exists_cofinal_structuralPairs
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ (Γ k : ℕ → Subgroup G) (m n r s : ℕ → ℕ) (d : (N : ℕ) → Fin (s N) → ℕ)
      (π : (N : ℕ) → ↥(Γ N) →* Multiplicative (ElemGroup (m N) (n N) (r N) (s N) (d N))),
      (∀ N, IsStructuralPair (Γ N) (k N) ∧ IsElemPresentation (Γ N) (k N) (π N)) ∧
      Monotone Γ ∧ Antitone k ∧
      ∀ (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')),
        IsStructuralPair Γ' k' → IsElemPresentation Γ' k' π' → ∃ M, Γ' ≤ Γ M ∧ k M ≤ k' := by
  sorry

end MasulloGRH
