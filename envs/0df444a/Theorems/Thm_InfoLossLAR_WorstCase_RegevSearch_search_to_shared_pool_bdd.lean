-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_shared_pool_bdd
-- name    : InfoLossLAR.WorstCase.RegevSearch.search_to_shared_pool_bdd
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T23:27:06.092581+00:00
-- url     : https://prove2.me/theorems/0bf36425-687f-493d-a04f-ac2e81e7e02e
-- title:
--   Bounded-distance decoding with a shared Gaussian pool from fixed-family LWE search
-- statement:
--   Suppose a uniform quantum circuit recovers each fixed secret with probability at least $3/4$ on a fresh polynomial-size table of the prescribed Gaussian LWE samples, for all sufficiently large $n$ in an infinite set $S$. Construct a single uniform quantum circuit family $C$, a polynomial $P$, a negligible function $e$, and a threshold. For every promised dimension beyond the threshold, fix a nonsingular integer basis $B$, a positive rational width $R>\sqrt{2}\,q_n\eta_{\varepsilon_n}(B\mathbb Z^n)$, a unary accuracy $k$, and a rational query $x$. Whenever a rational dual point $u$ satisfies $B^\top u=z\in\mathbb Z^n$ and $R^2\|x-u\|^2<\sigma_n^2/4$, the circuit must return the signed vector $z$ as a prefix with failure probability at most $e(n)+1/(k+1)$.
--
--   The probability averages the quantum measurement and the $P(n)$ independent coefficient vectors in one fresh Gaussian pool. The query is fixed before the pool is drawn. Each decoder execution can reuse the same pool throughout. A proof must connect the generated search tables to the discrete fixed-family noise law in `SearchOn`, justify the joint error under that reuse, and realize the public input and output encodings with a uniform circuit. A suffix after a complete signed-vector encoding is allowed.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, §3.2.1, Lemmas 3.4, 3.5, 3.7 and 3.11. These give the search-to-dual-decoding reduction, including recovery of full coordinates from residues. Matching the platform noise, the stated radius, common-pool probability, unary accuracy and circuit encoding are additional formalization obligations.

import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem search_to_shared_pool_bdd
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (A : MFamily) (hA : IsMQPT A) (samples : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A samples cutoff S) :
    ∃ C : MFamily, IsMQPT C ∧ ∃ P : Polynomial ℕ, ∃ error : ℕ → ℝ,
      Negligible error ∧ ∃ N : ℕ, SharedPoolBDD C P error N S := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
