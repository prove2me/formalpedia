-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_isStrictLFOfNuclearFrechet
-- name    : MasulloGRH.expDecaySchwartz_isStrictLFOfNuclearFrechet
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:44:35.654754+00:00
-- url     : https://prove2.me/theorems/9f637e12-90cf-4f55-af84-98f3d4ad2d69
-- title:
--   $\mathcal S_I(G)$ is a strict LF-space of nuclear Fréchet spaces
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $I\subset\mathbb R$ be a non-empty interval. Let $\mathcal S_I(G)$ be the space of continuous $\phi$ on $G$ with $|\cdot|_G^a\phi\in\mathcal S(G)$ for all $a\in I$. Give it the inductive topology of Definition D.3.3.3, which is the finest locally convex topology making the inclusions $\mathcal S_I(k,G)\hookrightarrow\mathcal S_I(G)$ continuous. Here $k$ runs over the good compact subgroups (compact, with compactly generated orthogonal), and $\mathcal S_I(k,G)$ carries the projective topology of the maps $T_a\colon\phi\mapsto|\cdot|_G^a\phi\in\mathcal S(G/k)$, $a\in I$.
--
--   Then $\mathcal S_I(G)$ is a **strict countable inductive limit of nuclear Fréchet spaces**. That is, there is an increasing sequence of subspaces $X_0\subseteq X_1\subseteq\cdots$ exhausting $\mathcal S_I(G)$ such that:
--   - each $X_N$, with the topology induced from $\mathcal S_I(G)$, is a nuclear Fréchet space;
--   - the topology of $\mathcal S_I(G)$ is the finest locally convex topology making all inclusions $X_N\hookrightarrow\mathcal S_I(G)$ continuous.
--
--   This is the analogue for $\mathcal S_I(G)$ of Bruhat's theorem `schwartzBruhat_isStrictLFOfNuclearFrechet` for $\mathcal S(G)$. It is the structural input to Theorem D.3.3.7(1). The steps are the spaces $\mathcal S_I(k_N,G)$ for a cofinal decreasing sequence of good subgroups $k_N$. Each step is Fréchet and nuclear, since its topology is defined by countably many maps $T_{a_j}$ ($a_j\in I$ accumulating at both ends of $I$) into the nuclear Fréchet spaces $\mathcal S(G/k_N)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.3.3.3 and Theorem D.3.3.7 with its proof (pp. 805–807); cf. Theorem D.1.5.7 and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961)

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem expDecaySchwartz_isStrictLFOfNuclearFrechet
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    IsStrictLFOfNuclearFrechet (ExpDecaySchwartz G m I) := by
  sorry

end MasulloGRH
