-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_shared_pool_bdd_to_gaussian_events
-- name    : InfoLossLAR.WorstCase.RegevSearch.shared_pool_bdd_to_gaussian_events
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T23:27:04.148981+00:00
-- url     : https://prove2.me/theorems/9fdfd0c1-342f-4e71-9410-562b6727463a
-- title:
--   One coefficient Gaussian sample from bounded-distance decoding with a shared pool
-- statement:
--   Fix an infinite set $S$ of positive dimensions and a uniform quantum decoder equipped with `CoherentPoolBDDBudget` on $S$. Construct a single uniform circuit family $H$ and a negligible $e$. For every sufficiently large $n\in S$, nonsingular integer basis $B$, positive rational $r$ at least `dgsThreshold B`, and unary accuracy $k$, run $H$ on the count-one input. With probability exactly one the measured word begins with the encoding of some signed coefficient vector. For every finite set $T\subset\mathbb Z^n$, the probability of a prefix encoding a member of $T$ differs from the ideal Gaussian coefficient mass of $T$ by at most $(e(n)+1/(k+1))/2$.
--
--   The proof must supply the broad initial samples, coherent decoder calls and uncomputation, and a width schedule reaching the requested rational width. The budget measures failure on a fixed reference query after averaging one shared Gaussian pool. A proof must justify its use on the ideal query superposition and the replacement of intermediate pools while preserving the joint computation. Every measured output of positive probability must have a valid signed-vector prefix, including outcomes of any truncated or fallback branch. Circuit output may carry padding after that prefix.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1, Lemma 3.3 and §3.2.2, Lemma 3.14. These motivate iteration and the quantum conversion from dual decoding to Gaussian sampling. The shared-pool error analysis, exact prefix validity, coefficient readout, arbitrary promised rational widths and the stated finite-event accuracy are additional formalization obligations.

import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem shared_pool_bdd_to_gaussian_events
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (C : MFamily) (hC : IsMQPT C) (P : Polynomial ℕ) (N : ℕ)
    (hbudget : CoherentPoolBDDBudget C P N S) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N' : ℕ, ∀ n ∈ S, N' ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ k : ℕ,
          let w := dgsInput B r 1 k
          outputProb H w (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1 ∧
          ∀ T : Finset (Fin n → ℤ),
            |outputProb H w (fun out => ∃ z ∈ T, encVec encI z <+: out) -
              ∑ z ∈ T, coefficientMass B r z| ≤ (e n + 1 / ((k : ℝ) + 1)) / 2 := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
