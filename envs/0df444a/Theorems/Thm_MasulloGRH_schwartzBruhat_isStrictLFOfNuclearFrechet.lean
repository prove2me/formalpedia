-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_isStrictLFOfNuclearFrechet
-- name    : MasulloGRH.schwartzBruhat_isStrictLFOfNuclearFrechet
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:48:59.717356+00:00
-- url     : https://prove2.me/theorems/c01d4430-9060-4ef1-89b2-b799f1d85c78
-- title:
--   Bruhat: $\mathcal S(G)$ is a strict LF-space of nuclear Fréchet spaces
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group and $\mathcal S(G)$ its Schwartz–Bruhat space, i.e. the union of the spaces $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ over all structural pairs $(\Gamma,k)$ (with $\Gamma$ open and compactly generated, $k\subseteq\Gamma$ a good subgroup, $\Gamma/k$ an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$), carrying the locally convex inductive limit topology of these spaces.
--
--   Then $\mathcal S(G)$ is a **strict countable inductive limit of nuclear Fréchet spaces**: there is an increasing sequence of subspaces $X_0\subseteq X_1\subseteq\cdots$ exhausting $\mathcal S(G)$ such that each $X_N$, with the topology induced from $\mathcal S(G)$, is a nuclear Fréchet space, and the topology of $\mathcal S(G)$ is the finest locally convex topology making all inclusions $X_N\hookrightarrow\mathcal S(G)$ continuous.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5.3, proof of Theorem D.1.5.7, pp. 763–764 (and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961))

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_isStrictLFOfNuclearFrechet
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    IsStrictLFOfNuclearFrechet (SchwartzBruhat G) := by sorry

end MasulloGRH
