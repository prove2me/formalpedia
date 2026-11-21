-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_diagonal_abs_sum_basis_independent
-- name    : MasulloGRH.nuclear_diagonal_abs_sum_basis_independent
-- status  : Disproved
-- author  : @marozols
-- created : 2026-11-21T00:51:59.995829+00:00
-- url     : https://prove2.me/theorems/9f438794-6b58-4f08-b6ea-d15d5c3fafc5
-- title:
--   Lemma C.3.4.1(2) as printed — basis independence of $\sum_\phi|\langle T\phi,\phi\rangle|$
-- statement:
--   This node records part (2) of Lemma C.3.4.1 of the draft **exactly as printed**, so that it can be checked.
--
--   Let $H$ be a Hilbert space and $T$ a nuclear (trace-class) operator on $H$. The printed statement is:
--
--   > *The value of the sum $\sum_{\phi\in\Sigma}|\langle T(\phi),\phi\rangle_H|$ is independent of the choice of* [the orthonormal basis] *$\Sigma$.*
--
--   Formally: for any two orthonormal bases $(\phi_i)_{i\in I_1}$ and $(\psi_j)_{j\in I_2}$ of $H$,
--   $$\sum_{i\in I_1}\bigl|\langle T\phi_i,\phi_i\rangle\bigr|=\sum_{j\in I_2}\bigl|\langle T\psi_j,\psi_j\rangle\bigr| .$$
--
--   Note that the absolute value is taken of each diagonal entry separately. This is different from part (3) of the same lemma (independence of $\sum_\phi\langle T\phi,\phi\rangle$, without absolute values), which is [nuclear_trace_hasSum_hilbertBasis](p2m:theorem/edf55f93-ccbe-48d2-b0cc-1ee9cc4c6e60), and from the trace norm $\sum_\phi\langle|T|\phi,\phi\rangle$ of Definition C.3.4.2(2).
--
--   **Formalization Note** The Hilbert space and the two index sets are taken in the lowest universe, which is enough to test the statement. Nuclearity is `IsNuclearOperator` from `Def_MasulloGRH_HilbertNuclear`; orthonormal bases are Mathlib's `HilbertBasis`. Mathlib's inner product is conjugate-linear in the first slot, so `inner ℂ (b i) (T (b i))` is $\langle T\phi_i,\phi_i\rangle$ in the draft's convention.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.4.1 part (2), p. 697

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_diagonal_abs_sum_basis_independent (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    (ι₁ ι₂ : Type) (b₁ : HilbertBasis ι₁ ℂ H) (b₂ : HilbertBasis ι₂ ℂ H) :
    ∑' i, ‖inner ℂ (b₁ i) (T (b₁ i))‖ = ∑' j, ‖inner ℂ (b₂ j) (T (b₂ j))‖ := by sorry

end MasulloGRH
