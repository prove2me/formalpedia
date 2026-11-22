-- Prove2me | Theorems.Thm_MasulloGRH_schauderBasis_equicontinuous_frechet_or_strictLF
-- name    : MasulloGRH.schauderBasis_equicontinuous_frechet_or_strictLF
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-11-21T07:42:58.425473+00:00
-- url     : https://prove2.me/theorems/81b4ced2-b23c-42d9-be7a-4c8925b4a790
-- title:
--   Equicontinuity of Schauder projections in Fréchet and strict LF spaces
-- statement:
--   Let $E$ be a Hausdorff locally convex complex vector space which is either a Fréchet space or a strict countable inductive limit of Fréchet spaces. Let $(x_m,f_m)$ be a Schauder basis with continuous coefficient functionals, and define
--   $$P_k u=\sum_{m=0}^{k} f_m(u)x_m.$$
--   Then $(P_k)$ is equicontinuous at zero: for every zero-neighborhood $U$ there is a zero-neighborhood $V$ such that $P_k(V)\subseteq U$ for every $k$. Nuclearity is not required for this topological step. The proof uses barrelledness and the uniform boundedness principle: each orbit $(P_k u)$ converges to $u$ and hence is bounded.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft linked 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 4.1.2.6 and its proof, printed p.161 (PDF page 161). Topological step in the proofs of parts (2) and (3), citing Jarchow, Part II, Ch.14, §14.3, Theorem 4 and Corollary 3, p.296; strict LF barrelledness is also cited there from Schaefer, Ch.II, §7.2, Corollary 2, p.61.

import Definitions.Def_MasulloGRH_SchauderBases
set_option autoImplicit false

theorem MasulloGRH.schauderBasis_equicontinuous_frechet_or_strictLF (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : MasulloGRH.IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : MasulloGRH.IsSchauderBasis x f)
    (hspace : MasulloGRH.IsFrechet E ∨ MasulloGRH.IsStrictLF E) :
    MasulloGRH.IsEquicontinuousBasis x f := by sorry
