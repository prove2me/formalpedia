-- Prove2me | Theorems.Thm_MasulloGRH_exists_small_good_subgroups
-- name    : MasulloGRH.exists_small_good_subgroups
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T14:02:21.946174+00:00
-- url     : https://prove2.me/theorems/f8d08a21-b632-40de-816a-4ac04833d3d9
-- title:
--   Small good subgroups with elementary quotients
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group. Recall that a closed subgroup $k\subseteq G$ is *good* if its annihilator $k^\perp\subseteq\widehat G$ is open and compactly generated, and that an elementary abelian Lie group is one of the form $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with $F$ finite abelian.
--
--   Then there is a decreasing sequence of good subgroups
--   $$k_0\supseteq k_1\supseteq k_2\supseteq\cdots$$
--   which **shrinks to the identity**, in the sense that every neighbourhood $U$ of $1$ contains some $k_N$, and such that for every $N$ and every open compactly generated subgroup $\Gamma\supseteq k_N$ the quotient $\Gamma/k_N$ is an elementary abelian Lie group. Concretely, there is a continuous open surjective homomorphism $\Gamma\to\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with kernel $k_N$.
--
--   This is the structural input for the Schwartz–Bruhat theory of $G$. It combines the structure theorem for compactly generated locally compact abelian groups ($\cong\mathbb R^a\times\mathbb Z^b\times K$ with $K$ compact) with Pontryagin duality for the compact part, which provides arbitrarily small closed subgroups with Lie quotients.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.4–D.1.5, pp. 757–764 (and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961); Hewitt–Ross, Abstract Harmonic Analysis I, §§9, 24)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem exists_small_good_subgroups
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ k : ℕ → Subgroup G, Antitone k ∧ (∀ U ∈ nhds (1 : G), ∃ N, (k N : Set G) ⊆ U) ∧
      (∀ N, IsGoodSubgroup (k N)) ∧
      ∀ (N : ℕ) (Γ : Subgroup G), IsOpen (Γ : Set G) → IsCompactlyGeneratedSubgroup Γ →
        k N ≤ Γ → ∃ (m n r s : ℕ) (d : Fin s → ℕ)
          (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)), IsElemPresentation Γ (k N) π := by
  sorry

end MasulloGRH
