-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
-- name    : MasulloGRH.schwartzBruhat_main_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:20:06.002184+00:00
-- url     : https://prove2.me/theorems/e3fa2914-8f53-4e5e-86af-ab87e2eeccc1
-- title:
--   Theorem D.1.5.7 — Main Structure Theorem on Schwartz–Bruhat spaces
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group and $\mathcal S(G)$ its Schwartz–Bruhat space, with the locally convex inductive limit topology of the spaces $\mathcal S(k,\Gamma)$. A Hausdorff locally convex space is **complete** if every Cauchy net converges, **nuclear** if for every Hausdorff locally convex space $F$ the projective and injective topologies on $E\otimes F$ coincide, **reflexive** if the canonical map $E\to(E'_\beta)'_\beta$ into the strong bidual is a topological isomorphism, and **Montel** if it is reflexive and every closed bounded subset is compact. $E'_\beta$ is the **strong dual**: the continuous dual with the topology of uniform convergence on bounded sets.
--
--   Then:
--
--   1. $\mathcal S(G)$ is a Hausdorff locally convex space, and it is barrelled and bornological.
--   2. $\mathcal S(G)$ is complete, nuclear and Montel.
--   3. The strong dual $\mathcal S(G)'_\beta$ is complete, nuclear, Montel and barrelled.
--
--   This is the theorem from which the draft derives the topological properties of all its spaces of Schwartz–Bruhat functions on adeles, ideles and idele classes.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5.3, Theorem D.1.5.7 (Main Structure Theorem on Schwartz-Bruhat spaces), pp. 763–764

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_main_structure
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    IsHLCS (SchwartzBruhat G) ∧
    BarrelledSpace ℂ (SchwartzBruhat G) ∧ IsBornological (SchwartzBruhat G) ∧
    IsCompleteTVS (SchwartzBruhat G) ∧ IsNuclear (SchwartzBruhat G) ∧ IsMontel (SchwartzBruhat G) ∧
    IsCompleteTVS (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsNuclear (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsMontel (StrongDual ℂ (SchwartzBruhat G)) ∧
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by sorry

end MasulloGRH
