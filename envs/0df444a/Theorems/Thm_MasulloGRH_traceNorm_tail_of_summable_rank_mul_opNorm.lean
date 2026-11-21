-- Prove2me | Theorems.Thm_MasulloGRH_traceNorm_tail_of_summable_rank_mul_opNorm
-- name    : MasulloGRH.traceNorm_tail_of_summable_rank_mul_opNorm
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:44:42.853978+00:00
-- url     : https://prove2.me/theorems/083952e2-a9f1-47a4-932a-c73bca3aa03b
-- title:
--   Trace-norm error of finite frequency-band truncations
-- statement:
--   Let $A_n$ be bounded operators on a complex Hilbert space, with range in finite-dimensional subspaces $S_n$. Suppose $\sum_n A_nu=Tu$ for every $u$ and $c_n=\dim(S_n)\|A_n\|$ is summable. For every finite index set $F$ the trace norm satisfies
--   $$
--   \left\|T-\sum_{n\in F}A_n\right\|_{\rm Tr}\le\sum_n c_n-\sum_{n\in F}c_n.
--   $$
--   In particular the finite sums converge to $T$ in trace norm as $F$ increases over the finite subsets. If the operators group nearby spectral values into bands, this gives the quantitative approximation error for truncating the bands.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, preprint pp. 67–68, equations (35)–(36), https://arxiv.org/abs/math/9811068. Quantitative trace-norm step for the fixed-line frequency-band proposal for Masullo §10.3.1 by Calvin Yost-Wolff, Prove2Me mission discussion, 20 November 2026, 22:19 UTC.

import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloGRH Filter
open scoped Topology BigOperators

theorem MasulloGRH.traceNorm_tail_of_summable_rank_mul_opNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (S : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (S n)]
    (hAS : ∀ n u, A n u ∈ S n)
    (hc : Summable (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖A n‖))
    (T : H →L[ℂ] H) (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    (∀ s : Finset ℕ, traceNorm (T - ∑ n ∈ s, A n) ≤
      (∑' n, (Module.finrank ℂ (S n) : ℝ) * ‖A n‖) -
      ∑ n ∈ s, (Module.finrank ℂ (S n) : ℝ) * ‖A n‖) ∧
    Tendsto (fun s : Finset ℕ => traceNorm (T - ∑ n ∈ s, A n)) atTop (𝓝 0) := by sorry
