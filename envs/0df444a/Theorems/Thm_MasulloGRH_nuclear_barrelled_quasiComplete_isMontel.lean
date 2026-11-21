-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_barrelled_quasiComplete_isMontel
-- name    : MasulloGRH.nuclear_barrelled_quasiComplete_isMontel
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:59:06.965547+00:00
-- url     : https://prove2.me/theorems/829f8956-1127-4d12-8c46-a5040809d711
-- title:
--   Nuclear barrelled quasi-complete spaces are Montel
-- statement:
--   Let $E$ be a nuclear, barrelled, quasi-complete complex locally convex space. Then $E$ is Montel: every closed bounded subset is compact, and the canonical evaluation map is a topological isomorphism onto the strong bidual,
--
--   $$E\cong(E'_\beta)'_\beta.$$
--
--   In particular each continuous functional $F$ on $E'_\beta$ has a unique representing point $x\in E$ with $F(f)=f(x)$ for all $f\in E'$, and the original topology of $E$ is the topology of uniform convergence on bounded subsets of $E'_\beta$.
--
--   This is the full nuclear barrelled quasi-complete Montel consequence stated before Lemma C.2.4.16, without any metrizability or countability hypothesis. Barrelledness is formalized by Mathlib's equivalent seminorm criterion: lower semicontinuous seminorms are continuous.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 690, paragraph immediately before Lemma C.2.4.16, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The paragraph explicitly cites Trèves, Corollary 3 to Proposition 50.2, for nuclear Hausdorff locally convex barrelled quasi-complete spaces being Montel. The mission IsMontel definition includes both compactness of closed bounded subsets and canonical topological reflexivity.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set

theorem MasulloGRH.nuclear_barrelled_quasiComplete_isMontel (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [BarrelledSpace ℂ E] (hE : IsQuasiComplete E) (hN : IsNuclear E) : IsMontel E := by sorry
