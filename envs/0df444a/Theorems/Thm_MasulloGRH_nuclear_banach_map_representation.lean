-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_banach_map_representation
-- name    : MasulloGRH.nuclear_banach_map_representation
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T23:18:57.413166+00:00
-- url     : https://prove2.me/theorems/7b1b204d-9555-418c-8b26-a3e281e98e6b
-- title:
--   Nuclear spaces admit absolutely summable expansions for all Banach-valued maps
-- statement:
--   Let $E$ be a nuclear complex Hausdorff locally convex space, and let $H$ be a complex Banach space. Every continuous linear map $u:E\to H$ admits a representation
--   $$u(x)=\sum_{n=0}^\infty c_n\varphi_n(x)v_n.$$
--   Here $\sum_n |c_n|<\infty$, the vectors $v_n$ belong to the closed unit ball of $H$, and one continuous seminorm $p$ on $E$ satisfies $|\varphi_n(x)|\le p(x)$ for all $n,x$. In particular the series converges absolutely in norm for each $x$.
--
--   In the hypothesis, nuclearity is expressed by equality of the projective and injective tensor topologies. Trèves’s characterization gives nuclearity of $u$, and the representation theorem for nuclear maps gives the displayed expansion after normalizing the bounded vectors. Taking $H$ to be the dual of a space with one continuous seminorm yields the Banach-valued representation needed in the abstract Schwartz kernel theorem.
-- source:
--   F. Trèves, Topological Vector Spaces, Distributions and Kernels (Academic Press, 1967), Theorem 50.1, (f) implies (c), p. 511, and Proposition 47.2, (a) implies (c), pp. 481–482. A. M. Masullo, The Music of the Primes, draft 20 November 2026, Appendix C, Theorem C.2.4.18, pp. 690–691.

import Definitions.Def_MasulloGRH_LocallyConvex

namespace MasulloGRH

theorem nuclear_banach_map_representation (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (hE : IsNuclear E) (u : E →L[ℂ] H) :
    ∃ (p : Seminorm ℂ E) (φ : ℕ → StrongDual ℂ E) (v : ℕ → H) (c : ℕ → ℂ),
      Continuous p ∧ (∀ n x, ‖φ n x‖ ≤ p x) ∧ (∀ n, ‖v n‖ ≤ 1) ∧
      Summable (fun n => ‖c n‖) ∧ ∀ x, HasSum (fun n => (c n * φ n x) • v n) (u x) := by sorry

end MasulloGRH
