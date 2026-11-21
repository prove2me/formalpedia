-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_frechet_isMontel
-- name    : MasulloGRH.nuclear_frechet_isMontel
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:49:12.304085+00:00
-- url     : https://prove2.me/theorems/a6a0760f-4dd5-45b8-a797-eeb1a25e6845
-- title:
--   Nuclear Fréchet spaces are Montel
-- statement:
--   Every complex nuclear Fréchet space $E$ is Montel. Explicitly, every closed bounded subset of $E$ is compact, and the canonical map into the strong bidual is a topological isomorphism:
--
--   $$E\ \cong\ (E'_\beta)'_\beta.$$
--
--   Thus each continuous linear functional $F$ on $E'_\beta$ is evaluation at a unique $x\in E$, and the original topology of $E$ equals the topology induced by uniform convergence on bounded subsets of $E'_\beta$.
--
--   This is the nuclear Fréchet case of the Montel consequence stated immediately before Masullo's Lemma C.2.4.16. It includes the canonical topological reflexivity assertion, in addition to the compactness and algebraic representation assertions.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 690, paragraph immediately before Lemma C.2.4.16 and the remark following it, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The paragraph cites Trèves, Corollary 3 to Proposition 50.2, for nuclear barrelled quasi-complete spaces being Montel, and notes all Fréchet spaces are barrelled. Here the conclusion is proved for the Fréchet case, with the mission definition IsMontel (compact closed bounded sets and canonical topological reflexivity).

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set

theorem MasulloGRH.nuclear_frechet_isMontel (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E) : IsMontel E := by sorry
