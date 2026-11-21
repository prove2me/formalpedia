-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_summable_rank_mul_opNorm
-- name    : MasulloGRH.nuclear_of_summable_rank_mul_opNorm
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:33:02.60137+00:00
-- url     : https://prove2.me/theorems/5dc39afd-0100-4f89-a43d-7b21b1518a38
-- title:
--   Nuclearity and trace of a sum of finite-rank operators
-- statement:
--   Let $H$ be a complex Hilbert space and let $A_n:H\to H$ be bounded linear operators. Suppose the range of $A_n$ lies in a finite-dimensional subspace $S_n$ and that $\sum_n A_nu=Tu$ for each $u\in H$. If $\sum_n \dim(S_n)\,\|A_n\|<\infty$, then $T$ is nuclear and
--   $$
--   \operatorname{Tr}(T)=\sum_n\operatorname{Tr}(A_n).
--   $$
--   The scalar series converges absolutely. The subspaces may overlap. This criterion allows estimates for entire frequency bands in the spectral nuclearity argument, even when the individual spectral vectors within a band are nearly linearly dependent.
-- source:
--   Auxiliary lemma for a frequency-band approach to A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, §10.3.1, Theorem 10.3.1.1(1), pp. 447–451, equations (10.3.1.7)–(10.3.1.20). The criterion is independently formulated here. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf The application to Masullo §10.3.1 follows the smooth-window proposal by Calvin Yost-Wolff in the Prove2Me mission discussion, 20 November 2026, 22:19 UTC (comment d8680fb7-dd35-4a9c-ab4e-5888ec240d48). See also A. Connes, Appendix I, equations (35)–(38), https://arxiv.org/abs/math/9811068.

import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloGRH

theorem MasulloGRH.nuclear_of_summable_rank_mul_opNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (S : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (S n)]
    (hAS : ∀ n u, A n u ∈ S n)
    (hc : Summable (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖A n‖))
    (T : H →L[ℂ] H) (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    IsNuclearOperator T ∧ HasSum (fun n => operatorTrace (A n)) (operatorTrace T) := by sorry
