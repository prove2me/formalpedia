-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_equicontinuous_basis_absolute
-- name    : MasulloGRH.nuclear_equicontinuous_basis_absolute
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-11-21T07:42:53.834379+00:00
-- url     : https://prove2.me/theorems/6b37eff4-84a4-468f-8ab3-04f65fca8afd
-- title:
--   Dynin–Mityagin criterion for equicontinuous Schauder bases
-- statement:
--   Let $E$ be a Hausdorff locally convex complex vector space, and let $(x_m,f_m)$ be a Schauder basis with continuous coefficient functionals. If $E$ is nuclear and the basic projections are equicontinuous at zero, then the basis is absolute: for every continuous seminorm $p$ there is a continuous seminorm $q$ such that, for every $u\in E$, the series below converges and satisfies
--   $$\sum_{m\ge0}p(f_m(u)x_m)\le q(u).$$
--   No completeness or metrizability assumption is imposed. This is the nuclearity step in Theorem 4.1.2.6(1); the existence of $q$ and summability are both part of the conclusion.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft linked 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 4.1.2.6 and its proof, printed p.161 (PDF page 161). Part (1), citing Jarchow, Locally Convex Spaces, Part III, Ch.21, §21.10, Theorem 1, p.510.

import Definitions.Def_MasulloGRH_SchauderBases
set_option autoImplicit false

theorem MasulloGRH.nuclear_equicontinuous_basis_absolute (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : MasulloGRH.IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : MasulloGRH.IsSchauderBasis x f)
    (hN : MasulloGRH.IsNuclear E) (heq : MasulloGRH.IsEquicontinuousBasis x f) :
    MasulloGRH.IsAbsoluteBasis x f := by sorry
