-- Prove2me | Theorems.Thm_MasulloGRH_trace_of_diagonal_frequency_bands
-- name    : MasulloGRH.trace_of_diagonal_frequency_bands
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:35:36.301408+00:00
-- url     : https://prove2.me/theorems/a8c1e845-e082-4a3b-82f2-f7a1aa911b9d
-- title:
--   A spectral trace formula for overlapping finite frequency bands
-- statement:
--   Let $(v_i)_{i\in I}$ be a linearly independent family whose linear span is dense in a complex Hilbert space $H$. Let $T$ and the operators $A_n$ be bounded, with $Tv_i=m_i v_i$ and $A_n v_i=a_{n,i}v_i$. Suppose that each row $(a_{n,i})_{i\in I}$ vanishes outside a finite band $F_n$, that $\sum_n a_{n,i}=m_i$ for every $i$, and that $\sum_n |F_n|\,\|A_n\|<\infty$.
--
--   Then $T$ is nuclear and its eigenvalues form an absolutely convergent family with
--   $$
--   \operatorname{Tr}(T)=\sum_{i\in I}m_i.
--   $$
--   This gives the pure-eigenvector case of the frequency localization used in the critical-line spectral trace. It applies to overlapping bands and requires no lower bound on the spacing of frequencies.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, preprint pp. 67–68, equations (35)–(38), https://arxiv.org/abs/math/9811068. Abstract pure-eigenvector form of the grouping argument, for comparison with A. M. Masullo, The Music of the Primes, §10.3.1, Theorem 10.3.1.1. The application to Masullo §10.3.1 follows the smooth-window proposal by Calvin Yost-Wolff in the Prove2Me mission discussion, 20 November 2026, 22:19 UTC (comment d8680fb7-dd35-4a9c-ab4e-5888ec240d48).

import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloGRH

theorem MasulloGRH.trace_of_diagonal_frequency_bands {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (hl : LinearIndependent ℂ v)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (F : ℕ → Finset ι) (A : ℕ → H →L[ℂ] H) (a : ℕ → ι → ℂ)
    (hA : ∀ n i, A n (v i) = a n i • v i)
    (hsupp : ∀ n i, i ∉ F n → a n i = 0)
    (hc : Summable fun n => ((F n).card : ℝ) * ‖A n‖)
    (T : H →L[ℂ] H) (m : ι → ℂ)
    (hpart : ∀ i, HasSum (fun n => a n i) (m i))
    (hT : ∀ i, T (v i) = m i • v i) :
    IsNuclearOperator T ∧ HasSum m (operatorTrace T) := by sorry
